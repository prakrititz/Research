"""A model-driven refiner for the Lean engine: show a goal, ask for one law, let Lean judge it, repeat.

    agent = LeanAgent(provider, max_calls=30, attempts_per_goal=4)
    result = agent.solve(task, lean_session)       # result.outcome: SOLVED | EXHAUSTED | NETWORK
    result.derivation.source()                      # the Lean program and its proof, if SOLVED

The same loop as the paper's (and as ``FormalLLM/agent/refiner.py``): pick an open goal, the model proposes a law with its
parameters, the engine checks the law's obligations, and a rejection comes back as the reason (Lean's unsolved goal, a
counter-example) for the next attempt on that goal. Differences that follow from the Lean core:

* the goal is shown the way Lean prints it (variables, hypotheses, ``⊢ ∃ ρ, …``), so the model sees what the prover sees;
* a reply may be one law or a nested derivation (``children``); the accepted prefix of a nested reply is kept;
* when a goal runs out of attempts, the law that created it is withdrawn (``Derivation.retract``) and the parent goal is
  tried again with the failure in its history, up to ``retractions`` times: this is the backtracking of the old agent, reduced
  to its one essential move.
"""
import json
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from FormalLLM.lean.engine import Certificate, Derivation, Step
from FormalLLM.lean.laws import Goal, HOLE, IllFormed, law_from_json
from FormalLLM.lean.session import LeanSession
from FormalLLM.lean.task import LeanTask
from FormalLLM.llm.transport import ENDPOINT_CUTOFF_MARKS, TRANSPORT_FAILURE_MARK

SOLVED, EXHAUSTED, NETWORK = "SOLVED", "EXHAUSTED", "NETWORK"

LAW_CARD = """You refine a specification into a Lean 4 program, one step at a time. A *goal* asks for a value ρ of a given
type that satisfies a property, in a context of variables and assumptions. You answer with ONE law, as a JSON object:

1. {"law": "term", "expr": "<Lean expression>"}
   The value is this expression. Lean must prove the property for it from the assumptions.
2. {"law": "cases", "cond": "<decidable Lean proposition>"}
   Split: one new goal where the condition is assumed, one where it is false. Use it when the answer differs by case.
3. {"law": "bind", "var": "<name>", "type": "<Lean type>", "prop": "<property of var>"}
   First find a value `var` with the property, then continue with it (and the property) available. Use it to compute
   something once and reuse it.
4. {"law": "loop", "state": [["i","Nat"],["acc","Int"]], "init": ["0","0"], "invariant": "<Prop over the state>",
   "guard": "<decidable Prop>", "variant": "<Nat expression that strictly decreases>", "result": "<expression>"}
   Start at `init`, repeat while `guard`; `invariant` must hold at the start and, with the guard false, must imply the
   goal's property for `result`. The new goal is the loop body: find the next state, keeping the invariant and making the
   variant smaller (usually answered by a `term` that is a tuple).

Any of these may also carry "lemmas": [{"name": "f_succ", "statement": "<Lean proposition>", "proof": "by …"}]: facts that Lean
proves first and then uses in the obligations (for example how a recursive definition in the specification unfolds one step).
A false lemma is refused.

Rules: Lean 4 syntax. `a[i]!` indexes (default value if out of range). `Nat` subtraction stops at 0. Names you introduce
(bind variable, loop state) must not already be in scope. Reply with the JSON object only."""

EXAMPLE = """Example. Goal: find ρ : Nat with 2 * ρ = n * (n + 1), given n : Nat. Answer:
{"law": "loop", "state": [["i","Nat"],["s","Nat"]], "init": ["0","0"], "invariant": "s * 2 = i * (i + 1) ∧ i ≤ n",
 "guard": "i < n", "variant": "n - i", "result": "s"}
The body goal is then: find (i', s') with the invariant and n - i' < n - i. Answer:
{"law": "term", "expr": "(i + 1, s + (i + 1))"}"""


def extract_json(reply: str) -> Optional[dict]:
    """The first JSON object in a reply (a code fence or surrounding words are tolerated)."""
    text = re.sub(r"```(?:json)?", "", reply or "")
    start = text.find("{")
    while start != -1:
        depth, in_string, escaped = 0, False, False
        for k in range(start, len(text)):
            ch = text[k]
            if in_string:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    in_string = False
            elif ch == '"':
                in_string = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    try:
                        value = json.loads(text[start:k + 1])
                        if isinstance(value, dict):
                            return value
                    except ValueError:
                        pass
                    break
        start = text.find("{", start + 1)
    return None


@dataclass
class Call:
    goal: int
    prompt: str
    reply: str
    outcome: str                        # applied | unparsable | ill_formed | unproved | timeout | network
    feedback: str = ""


@dataclass
class AgentResult:
    outcome: str
    derivation: Derivation
    calls: List[Call] = field(default_factory=list)
    certificate: Optional[Certificate] = None
    retractions: int = 0
    detail: str = ""

    @property
    def verified(self) -> bool:
        return self.outcome == SOLVED and self.certificate is not None and self.certificate.verified


class LeanAgent:
    def __init__(self, provider, max_calls: int = 30, attempts_per_goal: int = 4, retractions: int = 3,
                 max_tokens: int = 1024):
        self.provider, self.max_calls, self.attempts_per_goal = provider, max_calls, attempts_per_goal
        self.retractions, self.max_tokens = retractions, max_tokens

    # --- prompts --------------------------------------------------------------------------------------------------

    def describe(self, derivation: Derivation, goal: Goal) -> str:
        """The goal as Lean prints it: context, assumptions, then ``⊢ ∃ ρ : T, property``."""
        statement = f"theorem show_goal {goal.binders()} : ∃ ρ : {goal.ret}, {goal.post.replace(HOLE, 'ρ')} := by\n  (try dsimp only); sorry"
        reply = derivation.lean.run(statement, env=derivation._environment())
        if reply.goals:
            return reply.goals[0].strip()
        return f"{goal.binders()}\n⊢ ∃ ρ : {goal.ret}, {goal.post.replace(HOLE, 'ρ')}"

    def prompt(self, derivation: Derivation, goal: Goal, failures: List[str]) -> str:
        task = derivation.task
        parts = [LAW_CARD, EXAMPLE, "",
                 f"Task: {task.name}",
                 task.description[:1500], "",
                 "Definitions (Lean):", task.prelude.strip()[-2500:], "",
                 f"Goal {goal.id}: find ρ : {goal.ret}", self.describe(derivation, goal)]
        if failures:
            parts += ["", "Earlier attempts on this goal were rejected:"] + failures[-3:]
        parts += ["", "Your answer (one JSON object):"]
        return "\n".join(parts)

    # --- the loop -------------------------------------------------------------------------------------------------

    def solve(self, task: LeanTask, lean: LeanSession, derivation: Optional[Derivation] = None) -> AgentResult:
        derivation = derivation or Derivation(task, lean)
        result = AgentResult(EXHAUSTED, derivation)
        failures: Dict[int, List[str]] = {}
        attempts: Dict[int, int] = {}
        parent_of: Dict[int, int] = {}
        errors: List[str] = []
        while not derivation.complete:
            if len(result.calls) >= self.max_calls:
                result.detail = "out of model calls"
                break
            goal = derivation.open_goals()[0]
            if attempts.get(goal.id, 0) >= self.attempts_per_goal:
                parent = self._parent(derivation, goal.id)
                if parent is None or result.retractions >= self.retractions:
                    result.detail = f"goal {goal.id} failed {attempts[goal.id]} times"
                    break
                note = f"its sub-goal {goal.id} could not be solved after {attempts[goal.id]} attempts; choose a different step"
                failures.setdefault(parent, []).append(f"- the step you chose here was withdrawn: {note}")
                derivation.retract(parent)
                attempts[parent] = attempts.get(parent, 0) + 1
                result.retractions += 1
                continue
            attempts[goal.id] = attempts.get(goal.id, 0) + 1
            prompt = self.prompt(derivation, goal, failures.get(goal.id, []))
            try:
                reply = self.provider.generate(prompt, max_tokens=self.max_tokens)
            except Exception as error:                      # the provider raises once its own retries are used up
                message = str(error)
                errors.append(message)
                result.calls.append(Call(goal.id, prompt, "", "network", message[:200]))
                if any(mark in message for mark in ENDPOINT_CUTOFF_MARKS) or TRANSPORT_FAILURE_MARK in message:
                    result.outcome, result.detail = NETWORK, message[:200]
                    return result
                continue
            call = self._apply(derivation, goal, prompt, reply, failures)
            result.calls.append(call)
        if derivation.complete:
            result.certificate = derivation.certify()
            result.outcome = SOLVED if result.certificate.verified else EXHAUSTED
            if not result.certificate.verified:
                result.detail = "the finished term was not accepted: " + "; ".join(result.certificate.errors)[:200]
        return result

    def _apply(self, derivation: Derivation, goal: Goal, prompt: str, reply: str, failures: Dict[int, List[str]]) -> Call:
        data = extract_json(reply)
        if data is None:
            failures.setdefault(goal.id, []).append("- your reply contained no JSON object")
            return Call(goal.id, prompt, reply, "unparsable")
        steps: List[Step] = derivation.apply_tree(data, goal.id)
        last = steps[-1]
        if last.ok:
            return Call(goal.id, prompt, reply, "applied")
        text = last.feedback()
        # the failing step may be inside a nested reply: attribute the feedback to the goal it concerns
        target = goal.id
        failures.setdefault(target, []).append(f"- {json.dumps(data, ensure_ascii=False)[:300]}\n  {text[:900]}")
        return Call(goal.id, prompt, reply, last.status, text[:1500])

    @staticmethod
    def _parent(derivation: Derivation, goal_id: int) -> Optional[int]:
        for node_id, node in derivation.nodes.items():
            if any(child.goal.id == goal_id for child in node.children):
                return node_id
        return None
