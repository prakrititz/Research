"""The whole loop in L_spec: the model refines a task from its specification to a proved program, one step at a time,
writing every step in L_spec; the translator turns it into Lean, the prover checks it, and a refusal comes back in
L_spec.

    agent = LSpecAgent(provider, workflow="joint")      # or "split": a selector call, then an applier call
    result = agent.solve(task, lean)                    # result.outcome: SOLVED | EXHAUSTED | NETWORK

The loop is the Lean agent's (``agent.py``), with the model's side in L_spec:

* the goal is shown in L_spec (``steps.goal_to_lspec``; a loop body's goal names the next state ``i_next, ...``);
* a reply is one step in L_spec (``steps.FIELDS``), never a proof: the prover proves every obligation (the paper's
  protocol);
* a step Lean rejects only for a conversion Python would not need is repaired (``repair.py``) and checked again;
* a refusal is described in L_spec (``feedback.py``): unreadable, false (with a counter-example) or unproved;
* ``split``: a selector names the law, an applier writes it; an unproved step or a goal failing twice goes back to
  the selector (``feedback.recipient``);
* a goal out of attempts withdraws the step that created it and the parent is tried again (``retractions``);
* ``samples``: an attempt draws up to that many replies and keeps the first the prover accepts (best of n);
* ``max_binds``: a goal already under that many ``bind`` steps may not take another; a bind names a value for later
  use, and a chain of them only postpones the goal (a rule on the shape of the derivation, the same for every task).

``judge`` is the check of one step, shared with the per-step harness (``benchmarks/lspec_applier.py``)."""
import json
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from FormalLLM.dsl import feedback, prompts, repair, steps
from FormalLLM.lean.agent import EXHAUSTED, NETWORK, SOLVED, AgentResult, Call
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.laws import IllFormed, law_from_json
from FormalLLM.llm.transport import ENDPOINT_CUTOFF_MARKS, TRANSPORT_FAILURE_MARK

LEVELS = ("translate", "elaborate", "prove")


# --- one step --------------------------------------------------------------------------------------------------------

def scope_of(goal) -> list:
    return [n for n, _ in goal.ctx] + [n for n, _ in goal.hyps]


def elaboration_error(d: Derivation, goal, engine: dict):
    """The first obligation of ``engine`` (an engine step) at ``goal`` that does not type-check, with Lean's error;
    None when all do."""
    expansion = law_from_json(engine).expand(goal, lambda: 10 ** 6)
    for k, ob in enumerate(expansion.obligations):
        if ob.body is not None:
            verdict = d._check(ob, f"wf{goal.id}_{k}")
            error = None if verdict.proved else (verdict.message or verdict.status)
        else:
            reply = d._run(f"example {ob.binders} :\n    {ob.statement} := by\n  sorry\n")
            error = "timeout" if reply.timed_out else (reply.errors[0] if reply.errors else None)
        if error:
            return ob, error
    return None


def repaired(d: Derivation, goal, engine: dict, failure, rounds: int = 3):
    """``engine`` with the conversions Lean's errors call for (``repair.py``), when they make it type-check: (the
    repaired step, the reasons); None otherwise. A candidate that changes the error is kept for the next round."""
    current, notes = engine, []
    for _ in range(rounds):
        progress = None
        for candidate, why in repair.repairs(current, failure[1]):
            try:
                after = elaboration_error(d, goal, candidate)
            except (IllFormed, KeyError, TypeError, ValueError):
                continue
            if after is None:
                return candidate, notes + [why]
            if progress is None and after[1] != failure[1]:
                progress = (candidate, why, after)
        if progress is None:
            return None
        current, failure = progress[0], progress[2]
        notes.append(progress[1])
    return None


@dataclass
class Judgement:
    kind: str                                   # feedback.ACCEPTED | UNREADABLE | FALSE | UNPROVED
    message: str = ""                           # the refusal, in L_spec
    note: str = ""                              # what the translator converted (``repair.py``), if anything
    engine: Optional[dict] = None               # the step as applied (Lean text)


def _read(written: dict, goal, scope):
    """The step in Lean and its law, expanded at ``goal`` (raises when it cannot be read)."""
    engine = steps.to_engine(written, scope)
    law = law_from_json(engine)
    law.expand(goal, lambda: 10 ** 6)
    return engine, law


def judge(d: Derivation, goal, written: dict, level: str = "prove", loop_body: bool = False,
          use_repair: bool = True, lemmas: bool = False) -> Judgement:
    """Translate the model's step ``written`` and check it at ``goal`` to ``level``; at ``prove`` an accepted step
    stays applied in ``d``. Helper lemmas in the step are dropped (the model never writes proofs) unless ``lemmas``
    (checking the hand-written derivations, which bring some)."""
    scope = scope_of(goal)
    note = ""
    try:
        engine, law = _read(written, goal, scope)
    except (steps.StepError, IllFormed, KeyError, TypeError, ValueError) as error:
        typo = repair.text_repairs(written) if use_repair else None
        try:
            if typo is None:
                raise error
            engine, law = _read(typo[0], goal, scope)
            note = typo[1]
        except (steps.StepError, IllFormed, KeyError, TypeError, ValueError):
            return Judgement(feedback.UNREADABLE, feedback.unreadable(error))
    if level == "translate":
        return Judgement(feedback.ACCEPTED, note=note, engine=engine)
    failure = elaboration_error(d, goal, engine)
    if failure and use_repair:
        fixed = repaired(d, goal, engine, failure)
        if fixed:
            before, (engine, why) = engine, fixed
            law = law_from_json(engine)
            note = ("; ".join(([note] if note else []) + list(why)) + "\n"
                    + repair.describe(before, engine, lambda t: feedback._lspec(t, scope)))
            failure = None
    if failure:
        ob, error = failure
        shown = feedback.lean_error(error)
        return Judgement(feedback.UNREADABLE,
                         f"Lean cannot read the step: {ob.description}: this does not type-check.\n"
                         f"  {feedback._lspec(feedback.closed_statement(ob), scope)}\n"
                         f"  Lean's error: {shown}" + feedback.hints(shown, feedback.TYPE_HINTS))
    if level == "elaborate":
        return Judgement(feedback.ACCEPTED, note=note, engine=engine)
    result = d.apply(goal.id, law, (engine.get("lemmas") or ()) if lemmas else ())
    kind = feedback.kind_of(result)
    message = "" if result.ok else feedback.describe(result, loop_body, scope)
    if note and kind != feedback.ACCEPTED:
        message = f"(The translator read your step with conversions: {note.strip()})\n" + message
    return Judgement(kind, message, note, engine)


# --- positions in the derivation -------------------------------------------------------------------------------------

def parents(d: Derivation) -> Dict[int, object]:
    """goal id -> the node whose law created it."""
    out, stack = {}, [d.root]
    while stack:
        node = stack.pop()
        for child in node.children:
            out[child.goal.id] = node
            stack.append(child)
    return out


def path_of(d: Derivation, goal_id: int) -> str:
    """``0.1.0``: the goal's position, as ``benchmarks/lspec_steps.walk`` numbers the steps of a tree."""
    up = parents(d)
    parts, gid = [], goal_id
    while gid in up:
        parent = up[gid]
        parts.append(str([c.goal.id for c in parent.children].index(gid)))
        gid = parent.goal.id
    return ".".join(["0"] + parts[::-1])


def loop_state(d: Derivation, goal_id: int) -> Optional[List[str]]:
    """The state names when the goal is a loop's body (its first child), else None."""
    parent = parents(d).get(goal_id)
    if parent is not None and getattr(parent.law, "kind", "") == "loop" and parent.children[0].goal.id == goal_id:
        return [n for n, _ in parent.law.state]
    return None


def binds_above(d: Derivation, goal_id: int) -> int:
    up, count, gid = parents(d), 0, goal_id
    while gid in up:
        node = up[gid]
        count += getattr(node.law, "kind", "") == "bind"
        gid = node.goal.id
    return count


# --- the loop --------------------------------------------------------------------------------------------------------

@dataclass
class LSpecCall(Call):
    law: Optional[str] = None
    note: str = ""


class LSpecAgent:
    def __init__(self, provider, workflow: str = "joint", max_calls: int = 30, attempts_per_goal: int = 4,
                 retractions: int = 3, max_binds: int = 3, use_repair: bool = True, max_tokens: int = 4096,
                 examples: int = 0, pool: str = "cross", samples: int = 1, lemmas: bool = False):
        if workflow not in ("joint", "split"):
            raise ValueError("workflow: joint or split")
        self.lemmas = lemmas    # helper lemmas in a reply are proved and used: only for checking the gold derivations
        self.provider, self.workflow, self.max_calls = provider, workflow, max_calls
        self.attempts_per_goal, self.retractions, self.max_binds = attempts_per_goal, retractions, max_binds
        self.use_repair, self.max_tokens = use_repair, max_tokens
        self.examples, self.pool = examples, pool             # worked examples in the prompt (``examples.py``)
        self.samples = max(1, samples)                        # replies drawn per attempt (best of n)

    def _ask(self, prompt: str) -> str:
        return self.provider.generate(prompt, max_tokens=self.max_tokens)

    def solve(self, task, lean, derivation: Optional[Derivation] = None) -> AgentResult:
        d = derivation or Derivation(task, lean)
        result = AgentResult(EXHAUSTED, d)
        failures: Dict[int, List[str]] = {}
        attempts: Dict[int, int] = {}
        to_selector: Dict[int, bool] = {}
        chosen: Dict[int, Tuple[str, Optional[str]]] = {}
        while not d.complete:
            if len(result.calls) >= self.max_calls:
                result.detail = "out of model calls"
                break
            goal = d.open_goals()[0]
            if attempts.get(goal.id, 0) >= self.attempts_per_goal:
                parent = parents(d).get(goal.id)
                if parent is None or result.retractions >= self.retractions:
                    result.detail = f"goal {goal.id} failed {attempts[goal.id]} times"
                    break
                failures.setdefault(parent.goal.id, []).append(
                    f"The step you chose here was withdrawn: its sub-goal could not be solved after "
                    f"{attempts[goal.id]} attempts. Choose a different step.")
                d.retract(parent.goal.id)
                attempts[parent.goal.id] = attempts.get(parent.goal.id, 0) + 1
                to_selector[parent.goal.id] = True
                for gid in list(attempts):                  # the withdrawn sub-goals no longer exist
                    if gid not in d.nodes:
                        attempts.pop(gid)
                result.retractions += 1
                continue
            if hasattr(self.provider, "at_goal"):            # a scripted model (tests, gold) follows the position
                self.provider.at_goal(path_of(d, goal.id), scope_of(goal))
            state = loop_state(d, goal.id)
            shown = steps.goal_text(steps.goal_to_lspec(goal, state))
            try:
                calls = self._one_call(d, task, goal, shown, state, failures, chosen, to_selector)
            except Exception as error:                     # the provider raises once its own retries are used up
                message = str(error)
                result.calls.append(LSpecCall(goal.id, "", "", "network", message[:200]))
                if any(mark in message for mark in ENDPOINT_CUTOFF_MARKS) or TRANSPORT_FAILURE_MARK in message:
                    result.outcome, result.detail = NETWORK, message[:200]
                    return result
                continue
            result.calls.extend(calls)
            if calls[-1].outcome not in ("applied", "selected"):
                attempts[goal.id] = attempts.get(goal.id, 0) + 1
        if d.complete:
            result.certificate = d.certify()
            result.outcome = SOLVED if result.certificate.verified else EXHAUSTED
            if not result.certificate.verified:
                result.detail = "the finished term was not accepted: " + "; ".join(result.certificate.errors)[:200]
        return result

    def _one_call(self, d, task, goal, shown, state, failures, chosen, to_selector) -> List[LSpecCall]:
        """One attempt at ``goal``: in ``split``, the selector when the goal has no law yet (or a refusal went back
        to it), otherwise the applier (``samples`` replies, the first accepted one kept)."""
        from FormalLLM.dsl import examples
        past = failures.get(goal.id, [])

        def shown_examples(law=None):
            return examples.for_prompt(task, shown, law, self.examples, self.pool)
        if self.workflow == "split" and (goal.id not in chosen or to_selector.get(goal.id)):
            prompt = prompts.selector_prompt(task, shown, past, shown_examples())
            reply = self._ask(prompt)
            to_selector[goal.id] = False
            try:
                picked = prompts.parse_reply(reply)
                law, plan = str(picked.get("law")), picked.get("plan")
                steps.fields_for(law)
            except steps.StepError as error:
                text = feedback.unreadable(error)
                failures.setdefault(goal.id, []).append(f"Attempt: {reply[:300]}\n{text}")
                to_selector[goal.id] = True
                return [LSpecCall(goal.id, prompt, reply, "unreadable", text)]
            chosen[goal.id] = (law, plan)
            return [LSpecCall(goal.id, prompt, reply, "selected", law=law)]
        if self.workflow == "split":
            law, plan = chosen[goal.id]
            prompt = prompts.applier_prompt(task, shown, law, plan, past, shown_examples(law))
        else:
            law, prompt = None, prompts.joint_prompt(task, shown, past, shown_examples())
        calls, refused = [], []
        for _ in range(self.samples):                      # best of n: the first reply the prover accepts is kept
            call, text, kind = self._write(d, goal, prompt, law, state)
            calls.append(call)
            if call.outcome == "applied":
                return calls
            if text not in [t for t, _ in refused]:
                refused.append((text, kind))
        for text, kind in refused[:2]:                     # what the model reads next time: at most two refusals
            failures.setdefault(goal.id, []).append(text)
            if self.workflow == "split" and feedback.recipient(kind, len(failures[goal.id])) == "selector":
                to_selector[goal.id] = True
        return calls

    def _write(self, d, goal, prompt: str, law: Optional[str], state):
        """One reply at ``goal``, judged: (the call, the refusal as the model will read it, its kind)."""
        reply = self._ask(prompt)
        try:
            written = prompts.parse_reply(reply)
            if law is not None:
                written["law"] = law
        except steps.StepError as error:
            text = feedback.unreadable(error)
            return LSpecCall(goal.id, prompt, reply, "unreadable", text), f"Attempt: {reply[:300]}\n{text}", \
                feedback.UNREADABLE
        if written.get("law") == "bind" and binds_above(d, goal.id) >= self.max_binds:
            text = (f"Refused: this goal is already inside {self.max_binds} `bind` steps. A bind names a value to use "
                    f"later; another one only postpones the goal. Write the value (`term`), split on a condition "
                    f"(`cases`) or write a `loop`.")
            return (LSpecCall(goal.id, prompt, reply, "refused", text, law="bind"),
                    f"Attempt: {prompts.show_step(written)}\n{text}", feedback.UNREADABLE)
        verdict = judge(d, goal, written, "prove", loop_body=state is not None, use_repair=self.use_repair,
                        lemmas=self.lemmas)
        call = LSpecCall(goal.id, prompt, reply, "applied" if verdict.kind == feedback.ACCEPTED else verdict.kind,
                         verdict.message[:1500], law=written.get("law"), note=verdict.note)
        return call, f"Attempt: {prompts.show_step(written)}\n{verdict.message}", verdict.kind


class GoldModel:
    """Answers at every goal with the hand-written derivation's step there (in L_spec), so the whole loop is tested
    without a model: every task whose derivation the prover accepts must come out SOLVED."""
    name = "gold"

    def __init__(self, tree: dict):
        self.tree, self.path, self.scope = tree, "0", []

    def at_goal(self, path: str, scope):
        self.path, self.scope = path, scope

    def _step(self) -> dict:
        node = self.tree
        for k in self.path.split(".")[1:]:
            node = (node.get("children") or [])[int(k)]
        return {k: v for k, v in node.items() if k != "children"}

    def generate(self, prompt: str, max_tokens=None) -> str:
        step = self._step()
        if "Choose the law for this goal" in prompt:
            return json.dumps({"law": step["law"], "plan": ""})
        return json.dumps(steps.from_engine(step, self.scope), ensure_ascii=False)
