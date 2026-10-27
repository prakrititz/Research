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
import difflib
import json
import os
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
A false lemma is refused. In a proof, `auto_close` runs the project's automation on the current goal (use it for routine parts).

Rules: Lean 4 syntax. `a[i]!` indexes (default value if out of range). `Nat` subtraction stops at 0. Names you introduce
(bind variable, loop state) must not already be in scope. Reply with the JSON object only."""

EXAMPLE = """Example. Goal: find ρ : Nat with 2 * ρ = n * (n + 1), given n : Nat. Answer:
{"law": "loop", "state": [["i","Nat"],["s","Nat"]], "init": ["0","0"], "invariant": "s * 2 = i * (i + 1) ∧ i ≤ n",
 "guard": "i < n", "variant": "n - i", "result": "s"}
The body goal is then: find (i', s') with the invariant and n - i' < n - i. Answer:
{"law": "term", "expr": "(i + 1, s + (i + 1))"}"""

#: Which of the framework fixes are on (an ablation switch): 2 = Lean grounding in the prompt, 3 = name suggestions from the Lean
#: environment, 4 = retrieved worked examples, 5 = proof sub-agent for obligations the automation leaves open.
FIXES = set(os.environ.get("FORMALLLM_FIXES", "").replace(" ", "").split(",")) - {""}

#: Fix 6: a goal is shown the way Lean prints it, ``⊢ ∃ ρ, P ρ``, and a capable model then *proves* it: it put whole tactic
#: proofs into ``expr`` (34 of 39 failed calls in the first dev run). The value and its proof are now separate fields.
VALUE_AND_PROOF = """How to answer (important):
- `expr`, `init`, `invariant`, `guard`, `variant`, `result` are Lean *expressions*: the program and its annotations. Never put
  `by ...`, `⟨value, proof⟩`, `?_` or `Exists.intro` in them. The goal is shown as `∃ ρ, ...`, but you do not prove it:
  you give ρ.
- A `term` answer may add "proof": "by <tactics>". It proves the property OF YOUR VALUE: the goal's property with ρ
  replaced by `expr` (not `∃ ρ, ...`: the value is already chosen, so never start with `refine ⟨value, ?_⟩` or
  `exists`). The goal's variables and hypotheses are in scope; unfold the specification's definitions first
  (`unfold f_postcond` or `simp only [f_postcond]`). It is used only if the automation cannot prove the step.
  Example: {"law": "term", "expr": "Nat.primeFactorsList n", "proof": "by\\n  unfold factorize_postcond\\n  constructor\\n  · ..."}"""

_PROOF_IN_VALUE = re.compile(r"^\s*(by\b|Exists\.intro\b)|^\s*⟨[\s\S]*\bby\b|\?_")

LEAN_RULES = """Lean 4 rules (this is Lean 4.34 with Mathlib, not Lean 3):
- Functions are `fun x => e` (never `λ x, e`). Local values: `let x := e; body` (never `let ... in`).
- An expression cannot define a recursive function (`let rec`, recursive `match`). Repetition is the `loop` law's job.
- Values and conditions must run. A quantifier over all of `Nat` cannot run (`∃ i j : Nat, ...` is not decidable):
  bound each one, `∃ i < l.length, ∃ j < l.length, p i j` (that runs). `Classical`, `by_cases` belong in proofs only.
- Index with `a[i]!` (plain `a[i]` needs a bounds proof). `Nat` subtraction stops at 0; `/` on Nat and Int rounds down.
- Common names: `l.length`, `l.take n`, `l.drop n`, `l.map f`, `l.filter p`, `l.foldl f init`, `l.reverse`, `l.sum`,
  `List.range n`, `l.mergeSort (fun a b => decide (a ≤ b))` (there is no `List.sort`), `a.size`, `a.push x`, `a.toList`,
  `s.length`, `s.toList`. If unsure whether a name exists, use a loop over indices instead.
- State the invariant with the same functions and the same quantifier form as the postcondition: the final step
  "invariant and not guard imply the postcondition" is then mechanical.
- A helper lemma is a standalone theorem: the goal's variables are NOT in scope. Quantify everything it mentions,
  e.g. "∀ (l : List Int) (i : Nat), i < l.length → (l.take (i + 1)).sum = (l.take i).sum + l[i]!"."""

_UNDECIDABLE = re.compile(r"failed to synthesize[^\n]*\n\s*Decidable\s*\(?\s*[∃∀]")


def _error_hints(feedback: str) -> str:
    """Plain words for Lean errors the raw message does not explain to the model (it retried an unbounded `∃` 10 times)."""
    if _UNDECIDABLE.search(feedback):
        return ("\n  Hint: Lean cannot run a search over all natural numbers, so this condition has no Decidable instance. "
                "Bound every quantifier by a length: `∃ i < l.length, ∃ j < l.length, ...` runs; `∃ i j : Nat, ...` "
                "does not. `Classical`/`decide` on an unbounded quantifier do not help.")
    return ""


_LIBRARY = None


def library_card() -> str:
    """The proved lemmas of ``lemmas.py`` (``Refine.*``), one signature per line: the toolkit the hand-written derivations use."""
    global _LIBRARY
    if _LIBRARY is None:
        from FormalLLM.lean.lemmas import LEMMAS
        sigs = []
        for m in re.finditer(r"theorem (\w+)(.*?):=", LEMMAS, flags=re.S):
            sig = " ".join(m.group(2).split())
            if len(sig) < 260:
                sigs.append(f"Refine.{m.group(1)}{(' ' + sig) if sig else ''}")
        _LIBRARY = ("Proved library lemmas (the prover already rewrites with many of them; you may cite them in helper-lemma "
                    "proofs, e.g. `rw [Refine.take_succ_bang l i h]`):\n" + "\n".join(sigs))
    return _LIBRARY


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
                 max_tokens: int = 1024, max_syntax_per_goal: int = 12):
        self.provider, self.max_calls, self.attempts_per_goal = provider, max_calls, attempts_per_goal
        self.retractions, self.max_tokens = retractions, max_tokens
        self.max_syntax_per_goal = max_syntax_per_goal

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
        parts = [LAW_CARD, EXAMPLE, ""]
        if "6" in FIXES:
            parts += [VALUE_AND_PROOF, ""]
        if "2" in FIXES:
            parts += [LEAN_RULES, "", library_card(), ""]
        if "4" in FIXES:
            from FormalLLM.lean import retrieval
            shown = retrieval.examples(os.path.basename(task.directory.rstrip("/\\")), task.prelude)
            if shown:
                parts += ["Certified derivations of similar specifications from another benchmark (for the style of a good "
                          "answer; this task is different):", *shown, ""]
        parts += [f"Task: {task.name}",
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
        attempts: Dict[int, int] = {}              # real proof failures (unproved, timeout)
        syntax_fails: Dict[int, int] = {}          # ill_formed, unparsable, lemma errors (generous limit)
        parent_of: Dict[int, int] = {}
        engine_faults: Dict[int, int] = {}
        errors: List[str] = []
        self._proof_calls: Dict[int, int] = {}     # proof sub-agent calls per goal (capped: proofs must not eat the budget)
        self._rejected: Dict[int, set] = {}        # answers already refused at each goal (an exact repeat is not re-sent)
        while not derivation.complete:
            if len(result.calls) >= self.max_calls:
                result.detail = "out of model calls"
                break
            goal = derivation.open_goals()[0]
            real = attempts.get(goal.id, 0)
            syntax = syntax_fails.get(goal.id, 0)
            if real >= self.attempts_per_goal or syntax >= self.max_syntax_per_goal:
                parent = self._parent(derivation, goal.id)
                total = real + syntax
                if parent is None or result.retractions >= self.retractions:
                    result.detail = f"goal {goal.id} failed {total} times"
                    break
                note = f"its sub-goal {goal.id} could not be solved after {total} attempts; choose a different step"
                failures.setdefault(parent, []).append(f"- the step you chose here was withdrawn: {note}")
                derivation.retract(parent)
                attempts[parent] = attempts.get(parent, 0) + 1
                result.retractions += 1
                continue
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
            if call.outcome not in ("applied", "repeat") and getattr(self, "_last_key", None):
                self._rejected.setdefault(goal.id, set()).add(self._last_key)
            if call.outcome == "unproved" and "6" in FIXES and self._use_given_proof(derivation, goal, result, failures):
                continue                                # the model's own proof of its value closed the step
            if call.outcome == "unproved" and "5" in FIXES and len(result.calls) < self.max_calls:
                if self._prove_open_obligations(derivation, goal, call, result, failures):
                    continue                                # the step went through with proofs of its open obligations
            # Lean running out of time while *stating* an obligation is the engine's limit, not the model's mistake: do not
            # charge it to the goal (the call budget still bounds it)
            if call.outcome == "timeout" or "maximum number of heartbeats" in call.feedback:
                engine_faults[goal.id] = engine_faults.get(goal.id, 0) + 1
                if engine_faults[goal.id] <= 2:
                    continue
            # Separate budget: syntax errors (ill_formed, lemma_unproved) get a generous limit;
            # real proof failures (unproved, timeout) and unparsable replies count against per-goal attempts.
            if call.outcome in ('unproved', 'timeout', 'unparsable', 'repeat'):
                attempts[goal.id] = attempts.get(goal.id, 0) + 1
            elif call.outcome in ('ill_formed', 'lemma_unproved'):
                syntax_fails[goal.id] = syntax_fails.get(goal.id, 0) + 1
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
        self._last = (None, None)
        self._last_key = json.dumps(data, sort_keys=True, ensure_ascii=False)
        if self._last_key in getattr(self, "_rejected", {}).get(goal.id, set()):
            text = ("you sent exactly the same answer as before, and it was already rejected (see above): change the "
                    "expression, the invariant or the law")
            failures.setdefault(goal.id, []).append(f"- {text}")
            return Call(goal.id, prompt, reply, "repeat", text)
        if "6" in FIXES:
            bad = [k for k in ("expr", "init", "invariant", "guard", "variant", "result")
                   if isinstance(data.get(k), str) and _PROOF_IN_VALUE.search(data[k])]
            if bad:
                text = (f"`{bad[0]}` must be a plain Lean expression (the program value), but it contains a proof "
                        f"(`by`, `⟨_, _⟩`, `?_` or `Exists.intro`). Give the value in `{bad[0]}` and, for a term, the proof "
                        f"in a separate \"proof\" field.")
                failures.setdefault(goal.id, []).append(f"- {json.dumps(data, ensure_ascii=False)[:300]}\n  {text}")
                return Call(goal.id, prompt, reply, "ill_formed", text)
        steps: List[Step] = derivation.apply_tree(data, goal.id)
        last = steps[-1]
        if last.ok:
            return Call(goal.id, prompt, reply, "applied")
        text = last.feedback()
        if "3" in FIXES:
            text += self._name_hints(derivation, text) + _error_hints(text)
        self._last = (data, steps)
        # the failing step may be inside a nested reply: attribute the feedback to the goal it concerns
        target = goal.id
        failures.setdefault(target, []).append(f"- {json.dumps(data, ensure_ascii=False)[:300]}\n  {text[:900]}")
        return Call(goal.id, prompt, reply, last.status, text[:1500])

    # --- fix 3: names that exist ----------------------------------------------------------------------------------

    def _namespace_names(self, derivation: Derivation, ns: str) -> List[str]:
        cache = self.__dict__.setdefault("_ns_cache", {})
        if ns not in cache:
            src = ("open Lean in\n#eval show CoreM Unit from do\n  let env ← getEnv\n"
                   f"  let ns : Name := {json.dumps(ns)}.toName\n"
                   "  let names := env.constants.fold (fun acc n _ => if n.getPrefix == ns && !n.isInternal then "
                   "acc.push (n.toString) else acc) (#[] : Array String)\n"
                   "  IO.println (\" \".intercalate names.toList)\n")
            try:
                reply = derivation.lean.run(src, env=derivation._environment())
                text = " ".join(reply.infos)
            except Exception:
                text = ""
            cache[ns] = [n.rsplit(".", 1)[-1] for n in text.split()]
        return cache[ns]

    def _name_hints(self, derivation: Derivation, feedback: str) -> str:
        """For a name Lean does not know (``List.sort``), the closest names that *do* exist in that namespace."""
        wanted = re.findall(r"does not contain `([\w.']+)`", feedback)
        wanted += re.findall(r"[Uu]nknown (?:constant|identifier) `([\w.']+)`", feedback)
        hints = []
        for full in dict.fromkeys(wanted):
            if "." not in full or not full[0].isupper():
                continue
            ns, last = full.rsplit(".", 1)
            # definitions, not lemmas: Lean 4 names definitions in camelCase and theorems in snake_case
            names = [n for n in self._namespace_names(derivation, ns)
                     if "_" not in n and n[:1].islower() and not n.startswith("inst")]
            containing = sorted((n for n in names if last.lower() in n.lower()), key=len)
            close = list(dict.fromkeys(containing[:4] + difflib.get_close_matches(last, names, n=5, cutoff=0.55)))
            if close:
                hints.append(f"`{full}` does not exist; names in `{ns}` that do: " + ", ".join(f"`{ns}.{n}`" for n in close[:6]))
        return ("\n  Hint: " + "\n  Hint: ".join(hints)) if hints else ""

    # --- fix 5: a proof sub-agent for obligations the automation leaves open ---------------------------------------

    PROOF_CARD = ("Prove a theorem in Lean 4 (version 4.34, with Mathlib). The automation could not close it; you write the "
                  "tactic proof. Reply with a JSON object {\"proof\": \"by\\n  <tactics, one per line>\"} and nothing else. "
                  "Write the structure of the proof yourself (intro, constructor, rcases, cases, induction ... with, a witness with "
                  "refine ⟨w, ?_⟩, a key `have`), and close the routine parts with `auto_close`: the project's automation as one "
                  "tactic (arithmetic, list indexing, sorting, max/min of lists, gcd, the library lemmas below). Also available: "
                  "simp_all, omega, grind, exact, rw. Never use sorry, native_decide or axiom.")

    def _proof_provider(self):
        """The model that writes proofs: the refinement model, unless ``FORMALLLM_PROOF_CONFIG`` names a stronger one (the
        paper's split: the LLM refines, a strong prover proves)."""
        if not hasattr(self, "_prover"):
            name = os.environ.get("FORMALLLM_PROOF_CONFIG", "")
            self._prover = self.provider
            if name:
                from benchmarks import run_bench
                self._prover = run_bench.make_provider(run_bench.CONFIGS[name], 0.2)
        return self._prover

    @staticmethod
    def _binder_names(binders: str) -> Optional[List[str]]:
        names, depth, start = [], 0, None
        for k, ch in enumerate(binders):
            if ch in "{[" and depth == 0:
                return None                              # implicit or instance binders: intro would mis-count
            if ch == "(":
                if depth == 0:
                    start = k + 1
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and start is not None:
                    head = binders[start:k].split(":", 1)[0]
                    names += head.split()
        return names

    def _prove_one(self, derivation: Derivation, goal: Goal, verdict, result: "AgentResult",
                   seed: Optional[List[str]] = None) -> Optional[dict]:
        ob = verdict.obligation
        if self._binder_names(ob.binders) is None:
            return None
        name = f"ob{goal.id}_{len(result.calls)}"
        lemma, search_hint = self._library_search(derivation, name, ob)
        if lemma is not None:
            return lemma                                # proved by Lean's library search: no model call
        theorem = f"theorem {name} {ob.binders} :\n    {ob.statement}"
        history: List[str] = list(seed or [])
        for _ in range(3):
            proof_calls = getattr(self, "_proof_calls", {})
            if (len(result.calls) >= self.max_calls or proof_calls.get(goal.id, 0) >= 4
                    or sum(proof_calls.values()) >= self.max_calls // 2):
                return None                             # proofs may use at most 4 calls per goal and half the budget
            proof_calls[goal.id] = proof_calls.get(goal.id, 0) + 1
            prompt = "\n".join([self.PROOF_CARD, "", library_card(), "", "Theorem:", theorem, "",
                                "What is left after the automation (Lean's goal state):", *verdict.unsolved[:2],
                                *(["", search_hint] if search_hint else []),
                                *(["", "Your earlier attempts failed:"] + history[-2:] if history else []), "",
                                "Your answer (one JSON object):"])
            try:
                reply = self._proof_provider().generate(prompt, max_tokens=self.max_tokens)
            except Exception:
                return None
            data = extract_json(reply)
            proof = (data or {}).get("proof")
            if not isinstance(proof, str) or not proof.strip():
                result.calls.append(Call(goal.id, prompt, reply, "proof_unparsable"))
                history.append("- the reply had no JSON object with a \"proof\"")
                continue
            lemma, message = self._check_proof(derivation, name, ob, proof)
            result.calls.append(Call(goal.id, prompt, reply, "proof_ok" if lemma else "proof_failed", message))
            if lemma is not None:
                return lemma
            history.append(f"- {proof[:400]}\n  Lean: {message}")
        return None

    def _check_proof(self, derivation: Derivation, name: str, ob, proof: str) -> Tuple[Optional[dict], str]:
        """Check a tactic ``proof`` of obligation ``ob``; on success return it as a helper lemma closed over the context.

        The goal state the model is shown has the specification's definitions unfolded, but the theorem states them folded
        (``f_postcond x (value) h``), so a proof written against what the model saw fails at its first ``intro``. A failed
        proof is therefore tried once more after ``unfold`` of the task's pre/postcondition: a free Lean check, no model call."""
        from FormalLLM.lean.engine import HelperLemma
        names = self._binder_names(ob.binders)
        if names is None:
            return None, "the goal has implicit binders"
        try:
            body = HelperLemma.from_json({"name": name, "statement": "True", "proof": proof}).proof
        except Exception as error:
            return None, str(error)
        lines = body.split("\n")
        indent = min((len(l) - len(l.lstrip()) for l in lines[1:] if l.strip()), default=2) or 2
        task = derivation.task
        unfold = " " * indent + f"(try unfold {task.post_name} {task.pre_name} at *)"
        # the model is shown the goal as Lean prints it after ``dsimp only`` (lambdas applied, ``(fun i b => P i b) (i+1) x``
        # reduced to ``P (i+1) x``); the stored obligation is the unreduced form, where ``constructor``, ``right``, ``rcases``
        # on it fail. The same normalisation is therefore offered before the model's own tactics
        beta = " " * indent + "(try dsimp only at *)"
        theorem = f"theorem {name} {ob.binders} :\n    {ob.statement}"
        message = ""
        for variant in (lines, [lines[0], unfold] + lines[1:], [lines[0], unfold, beta] + lines[1:]):
            reply = derivation._run(f"set_option maxHeartbeats 400000 in\n{theorem} := " + "\n".join(variant) + "\n")
            if not (reply.timed_out or reply.errors or reply.goals):
                intro = [" " * indent + "intro " + " ".join(names)] if names else []
                statement = f"∀ {ob.binders}, {ob.statement}" if ob.binders.strip() else ob.statement
                return {"name": name, "statement": statement, "proof": "\n".join([variant[0]] + intro + variant[1:])}, ""
            # report the error against the normalised goal (the one the model saw), i.e. of the last variant tried
            message = "timeout" if reply.timed_out else (reply.errors[0][:700] if reply.errors else
                                                          "unsolved: " + reply.goals[0][:700])
        if "3" in FIXES:
            message += self._name_hints(derivation, message)
        return None, message

    def _library_search(self, derivation: Derivation, name: str, ob) -> Tuple[Optional[dict], str]:
        """Lean's own library search (``exact?``) on each part of the obligation, before any model call (the paper's prover
        is CoqHammer, a library search). If it closes every part, the obligation is proved for free; otherwise the lemmas it
        found for some parts become hints for the model."""
        task = derivation.task
        script = "\n".join(["by", f"  (try unfold {task.post_name} {task.pre_name} at *)", "  (try dsimp only at *)",
                            "  (repeat' apply And.intro)", "  all_goals (first | omega | (simp_all; done) | exact? | skip)"])
        theorem = f"theorem {name} {ob.binders} :\n    {ob.statement}"
        try:
            reply = derivation.lean.run(f"set_option maxHeartbeats 1000000 in\n{theorem} := {script}\n",
                                        timeout=240, env=derivation._environment())
        except Exception:
            return None, ""
        found = [i.strip() for i in reply.infos if "Try this" in i]
        if not (reply.timed_out or reply.errors or reply.goals):
            lemma, _ = self._check_proof(derivation, name, ob, script)
            if lemma is not None:
                return lemma, ""
        if not found:
            return None, ""
        return None, "Lean's library search found, for some parts of it:\n  " + "\n  ".join(f[:300] for f in found[:4])

    def _as_helper(self, derivation: Derivation, name: str, verdict, proof: str) -> Tuple[Optional[dict], str]:
        return self._check_proof(derivation, name, verdict.obligation, proof)

    def _use_given_proof(self, derivation: Derivation, goal: Goal, result: "AgentResult", failures: Dict[int, List[str]]) -> bool:
        """A ``term`` the automation could not prove, sent with the model's own ``proof``: let Lean check that proof."""
        data, steps = getattr(self, "_last", (None, None))
        if not data or data.get("law") != "term" or not isinstance(data.get("proof"), str) or len(steps) != 1:
            return False
        open_ = [v for v in steps[0].verdicts if v.status == "UNPROVED"]
        if len(open_) != 1 or any(v.status in ("ILL_FORMED", "TIMEOUT") for v in steps[0].verdicts):
            return False
        verdict = open_[0]
        lemma, message = self._as_helper(derivation, f"given{goal.id}_{len(result.calls)}", verdict, data["proof"])
        if lemma is None and "5" in FIXES:
            # one-shot proof failed: continue it in the proof sub-agent, starting from this attempt and Lean's error
            lemma = self._prove_one(derivation, goal, verdict, result,
                                    seed=[f"- {data['proof'][:400]}\n  Lean: {message[:600]}"])
        if lemma is None:
            failures.setdefault(goal.id, []).append(
                f"- your value was not proved by the automation, and your \"proof\" failed in Lean: {message[:600]}\n"
                f"  The proof must prove exactly: {verdict.obligation.binders} ⊢ {verdict.obligation.statement[:400]}")
            return False
        existing = {h.name for h in derivation.helpers}
        again = {k: v for k, v in data.items() if k != "proof"}
        again["lemmas"] = [l for l in (data.get("lemmas") or []) if isinstance(l, dict) and l.get("name") not in existing] + [lemma]
        return derivation.apply_tree(again, goal.id)[-1].ok

    def _prove_open_obligations(self, derivation: Derivation, goal: Goal, call: Call, result: "AgentResult",
                                failures: Dict[int, List[str]]) -> bool:
        """The step was refused only because the automation left obligations open (no counter-example, nothing ill-formed):
        have the model prove each one, then submit the same step again with those proofs as helper lemmas."""
        data, steps = getattr(self, "_last", (None, None))
        if data is None or len(steps) != 1 or data.get("children"):
            return False
        verdicts = steps[0].verdicts
        if any(v.status in ("ILL_FORMED", "TIMEOUT") for v in verdicts):
            return False
        open_ = [v for v in verdicts if v.status == "UNPROVED"]
        if not open_ or len(open_) > 2 or any(v.counterexample for v in open_):
            return False                                # a counter-example means the step is wrong, not unproved
        helpers = []
        for verdict in open_:
            lemma = self._prove_one(derivation, goal, verdict, result)
            if lemma is None:
                return False
            helpers.append(lemma)
        existing = {h.name for h in derivation.helpers}
        again = dict(data)
        again["lemmas"] = [l for l in (data.get("lemmas") or []) if isinstance(l, dict) and l.get("name") not in existing] + helpers
        steps2 = derivation.apply_tree(again, goal.id)
        if steps2[-1].ok:
            return True
        failures.setdefault(goal.id, []).append(f"- {json.dumps(data, ensure_ascii=False)[:300]}\n  "
                                                f"(its open obligations were proved, but the step still failed) {steps2[-1].feedback()[:600]}")
        return False

    @staticmethod
    def _parent(derivation: Derivation, goal_id: int) -> Optional[int]:
        for node_id, node in derivation.nodes.items():
            if any(child.goal.id == goal_id for child in node.children):
                return node_id
        return None
