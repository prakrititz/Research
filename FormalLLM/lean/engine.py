"""The Lean refinement engine: apply a law to a goal, have Lean judge its obligations, and certify a finished derivation.

    task = LeanTask.from_dir(...)
    with LeanSession() as lean:
        derivation = Derivation(task, lean)
        step = derivation.apply(derivation.root.goal.id, Loop(...))          # Lean checks the obligations
        if not step.ok:
            print(step.feedback())                                            # what Lean could not prove, and why
        ...
        certificate = derivation.certify()                                   # compile the whole term, #print axioms, run tests

Three layers of defence, the same idea as the earlier Z3 + Coq pair but with one prover: (1) each law's obligations are
proved on their own, so a wrong step is rejected where it is made; (2) the finished tree is one Lean term of type
``{ ρ : T // post }`` whose elaboration re-checks every obligation in context; (3) ``#print axioms`` must not list
``sorryAx``, and the program is run on the task's tests.
"""
import re
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from FormalLLM.lean.laws import (Goal, HOLE, IllFormed, Law, Obligation, Rendered, RESULT, law_from_json)
from FormalLLM.lean.lemmas import LEMMAS, SIMP_SET
from FormalLLM.lean.session import LeanSession
from FormalLLM.lean.task import LeanTask

def make_cascade(extra_simp=()):
    """The tactic that proves an obligation, and its *diagnosis* form (a part no tactic closes becomes ``sorry``, so that
    Lean reports its goal state). It reduces ``fun`` redexes and projections, splits conjunctions, then tries each tactic in
    turn. ``Refine.*`` are the lemmas of ``lemmas.py``; ``extra_simp`` are helper lemmas a step brought along."""
    simp = ", ".join([SIMP_SET, *extra_simp])
    # helper lemmas are used three ways: as rewrite rules (above); by ``apply`` when the goal is one of their conclusions (the
    # hypotheses are then discharged by ``simp_all``); and by ``grind``, which instantiates them by pattern
    helpers = ""
    if extra_simp:
        names = ", ".join(extra_simp)
        applied = " | ".join(f"(apply {n} <;> simp_all)" for n in extra_simp)
        helpers = f"{applied} | (grind [{names}]) | (simp_all [{simp}] <;> grind [{names}]) | "
    tactic = ("(try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | "
              f"(simp_all [{simp}]; done) | (simp_all [{simp}]; omega) | (simp_all; omega) | "
              f"(simp_all [{simp}, Nat.mul_comm]; done) | (simp_all [{simp}, mul_assoc]; done) | "
              f"(split <;> simp_all [{simp}]; done) | "
              f"(split_ifs <;> simp_all [{simp}] <;> omega) | (simp_all [{simp}, Nat.mul_comm, Nat.mul_left_comm]; done) | "
              + helpers + "nlinarith | (aesop; done))")
    return tactic, tactic[:-1] + " | sorry)"


CASCADE, DIAGNOSE = make_cascade()
LEMMA_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def _tactic_block(proof: str) -> str:
    """``by tac1\n  tac2`` is not a tactic block in Lean (the first tactic sits after ``by``, the others at column 2);
    people and models write it that way. Put the first tactic on its own line at the indent of the others."""
    lines = proof.splitlines()
    if len(lines) < 2 or not lines[0].startswith("by"):
        return proof
    first, rest = lines[0][2:].strip(), lines[1:]
    indents = [len(line) - len(line.lstrip()) for line in rest if line.strip()]
    indent = min(indents) if indents else 2
    if indent == 0:
        rest, indent = ["  " + line if line.strip() else line for line in rest], 2
    return "by\n" + (" " * indent + first + "\n" if first else "") + "\n".join(rest)


@dataclass(frozen=True)
class HelperLemma:
    """A fact a step brings along because the cascade cannot find it (the paper's authors supplied such lemmas to Coq by
    hand). Lean proves it like any theorem, so a false lemma is rejected; an accepted one joins the simp set."""
    name: str
    statement: str
    proof: str                        # ``by …`` or a term

    def source(self) -> str:
        return f"set_option maxHeartbeats 400000 in\ntheorem {self.name} : {self.statement} := {self.proof}\n"

    @staticmethod
    def from_json(data: dict) -> "HelperLemma":
        try:
            name, statement, proof = str(data["name"]), str(data["statement"]), str(data["proof"])
        except (KeyError, TypeError) as missing:
            raise IllFormed(f"a helper lemma needs name, statement and proof ({missing})")
        if not LEMMA_NAME.fullmatch(name):
            raise IllFormed(f"{name!r} is not a usable lemma name")
        if not statement.strip() or not proof.strip():
            raise IllFormed("a helper lemma needs a statement and a proof")
        proof = proof.strip()
        if proof.startswith(":="):
            proof = proof[2:].strip()
        if not proof.startswith("by"):
            proof = "by " + proof
        return HelperLemma(name, statement, _tactic_block(proof))


#: ``plausible`` needs instances for long implications; the default size limit is too small for them.
#: A fixed seed: the same wrong step gets the same counter-example in every run (a result must be replayable).
PLAUSIBLE_CONFIG = "(config := { randomSeed := some 20261008, numInst := 200 })"
TESTING = "set_option synthInstance.maxSize 100000 in\nset_option synthInstance.maxHeartbeats 0 in\n"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
PRINT_AXIOMS = re.compile(r"depends on axioms: \[(.*?)\]", re.S)


@dataclass
class Verdict:
    obligation: Obligation
    status: str                                   # PROVED | UNPROVED | ILL_FORMED | TIMEOUT
    message: str = ""
    unsolved: List[str] = field(default_factory=list)     # goal states of the parts no tactic closed
    counterexample: Optional[str] = None
    seconds: float = 0.0

    @property
    def proved(self) -> bool:
        return self.status == "PROVED"


@dataclass
class Step:
    ok: bool
    status: str                                   # applied | ill_formed | unproved | timeout | unknown_goal
    message: str = ""
    verdicts: List[Verdict] = field(default_factory=list)
    subgoals: List[Goal] = field(default_factory=list)

    def feedback(self) -> str:
        """What a person (or a model) needs to repair the step."""
        if self.ok:
            return "accepted"
        lines = [self.message] if self.message else []
        for verdict in self.verdicts:
            if verdict.proved:
                continue
            lines.append(f"- {verdict.obligation.description}: {verdict.status.lower().replace('_', ' ')}")
            lines.append(f"  to prove: {verdict.obligation.statement}")
            if verdict.message:
                lines.append(f"  Lean: {verdict.message}")
            for goal in verdict.unsolved[:2]:
                lines.append("  not closed:\n    " + goal.replace("\n", "\n    "))
            if verdict.counterexample:
                shown = verdict.counterexample
                text = shown if shown.startswith("counter-example") else f"counter-example: {shown}"
                lines.append("  " + text.replace("\n", "\n  "))
        return "\n".join(lines)


@dataclass
class Node:
    goal: Goal
    law: Optional[Law] = None
    children: List["Node"] = field(default_factory=list)
    verdicts: List[Verdict] = field(default_factory=list)


@dataclass
class Certificate:
    compiles: bool
    errors: List[str] = field(default_factory=list)
    axioms: Optional[str] = None                  # what ``#print axioms`` listed; ``None`` if it printed nothing
    tests: int = 0
    passed: int = 0
    seconds: float = 0.0

    @property
    def sound(self) -> bool:
        """It compiled and the specification theorem rests on Lean's three standard axioms only: no ``sorryAx``, no
        ``Lean.ofReduceBool`` (``native_decide``), no axiom a step might have declared."""
        if not self.compiles or self.axioms is None:
            return False
        used = {name.strip() for name in self.axioms.split(",") if name.strip()}
        return used <= STANDARD_AXIOMS

    @property
    def verified(self) -> bool:
        """A proof the kernel accepts and a program that passes every test of the task."""
        return self.sound and self.tests > 0 and self.passed == self.tests


class Derivation:
    def __init__(self, task: LeanTask, lean: LeanSession, tactic: Optional[str] = None, diagnose: Optional[str] = None,
                 counterexamples: bool = True, timeout: float = 90.0, lemmas: str = LEMMAS):
        self.task, self.lean = task, lean
        self._tactic, self._diagnose = tactic, diagnose            # None: the cascade, extended by accepted helper lemmas
        self.lemmas = lemmas
        self.helpers: List[HelperLemma] = []
        self.counterexamples, self.timeout = counterexamples, timeout
        self._next = 0
        root = Goal(self._fresh(), tuple((n, t) for n, t in task.params),
                    (("h_precond", f"{task.pre_name} {task.args}"),), task.ret, task.root_post)
        self.nodes: Dict[int, Node] = {root.id: Node(root)}
        self.root = self.nodes[root.id]
        self._memo: Dict[str, Verdict] = {}
        self._env_id: Optional[int] = None
        self._env_restarts = -1
        self.lean_seconds = 0.0

    def _fresh(self) -> int:
        self._next += 1
        return self._next

    @property
    def tactic(self) -> str:
        return self._tactic or make_cascade([h.name for h in self.helpers])[0]

    @property
    def diagnose(self) -> str:
        return self._diagnose or make_cascade([h.name for h in self.helpers])[1]

    def _helper_text(self) -> str:
        return "\n".join(h.source() for h in self.helpers)

    # --- the tree -------------------------------------------------------------------------------------------------

    def open_goals(self) -> List[Goal]:
        out, stack = [], [self.root]
        while stack:
            node = stack.pop(0)
            if node.law is None:
                out.append(node.goal)
            stack = node.children + stack if node.children else stack
        return out

    @property
    def complete(self) -> bool:
        return not self.open_goals()

    @property
    def laws_used(self) -> int:
        return sum(1 for node in self.nodes.values() if node.law is not None)

    # --- judging a step -------------------------------------------------------------------------------------------

    def _environment(self) -> int:
        """The Lean environment holding the task's definitions (loaded once; again after a restart of the session)."""
        if self._env_id is None or self._env_restarts != self.lean.restarts:
            reply, env = self.lean.load(self.lemmas + "\n" + self.task.prelude + "\n" + self._helper_text())
            if env is None:
                raise ValueError("the task's own definitions do not compile: " + (reply.errors or ["?"])[0][:300])
            self._env_id, self._env_restarts = env, self.lean.restarts
        return self._env_id

    def _run(self, source: str):
        started = time.time()
        reply = self.lean.run(source, timeout=self.timeout, env=self._environment())
        self.lean_seconds += time.time() - started
        return reply

    def _check(self, obligation: Obligation, name: str) -> Verdict:
        source = obligation.source(name, self.diagnose)
        if source in self._memo:
            return self._memo[source]
        reply = self._run(source)
        if reply.timed_out:
            verdict = Verdict(obligation, "TIMEOUT", "Lean gave no answer within the time limit", seconds=reply.seconds)
        elif reply.errors:
            verdict = Verdict(obligation, "ILL_FORMED", reply.errors[0][:600], seconds=reply.seconds)
        elif reply.goals:
            verdict = Verdict(obligation, "UNPROVED", "no tactic of the cascade closes this", unsolved=reply.goals,
                              seconds=reply.seconds)
            if self.counterexamples:
                verdict.counterexample = self._counterexample(obligation, name)
        else:
            verdict = Verdict(obligation, "PROVED", seconds=reply.seconds)
        self._memo[source] = verdict
        return verdict

    def _counterexample(self, obligation: Obligation, name: str) -> Optional[str]:
        source = (TESTING + f"theorem {name}_cex {obligation.binders} :\n    {obligation.statement} := by\n"
                  f"  (try dsimp only at *); plausible {PLAUSIBLE_CONFIG}\n")
        reply = self._run(source)
        return reply.counterexample

    def _admit(self, lemma: HelperLemma) -> Optional[Verdict]:
        """Have Lean prove a helper lemma; ``None`` when it is accepted (and now part of the environment)."""
        if any(h.name == lemma.name for h in self.helpers):
            return Verdict(Obligation("lemma", f"helper lemma {lemma.name}", "", lemma.statement), "ILL_FORMED",
                           f"a helper lemma named {lemma.name} already exists")
        obligation = Obligation("lemma", f"helper lemma {lemma.name}", "", lemma.statement)
        reply = self._run(lemma.source())
        if reply.timed_out:
            return Verdict(obligation, "TIMEOUT", "Lean gave no answer within the time limit", seconds=reply.seconds)
        if reply.errors or reply.goals:
            message = reply.errors[0][:600] if reply.errors else "the proof uses sorry"
            return Verdict(obligation, "UNPROVED", message, seconds=reply.seconds)
        self.helpers.append(lemma)
        self._env_id = None                       # the next command reloads the environment with the lemma in it
        return None

    def _parent_of(self, goal_id: int) -> Optional[Node]:
        for node in self.nodes.values():
            if any(child.goal.id == goal_id for child in node.children):
                return node
        return None

    def _run_the_loop(self, node: Node, law: Law, bad: List[Verdict]) -> None:
        """For a step of a loop that was refused, replace a missing or weak counter-example by a run of the loop (``dynamic.py``)."""
        from FormalLLM.lean import dynamic
        from FormalLLM.lean.laws import Loop, Term
        finding = None
        try:
            if isinstance(law, Term):
                parent = self._parent_of(node.goal.id)
                if parent is not None and isinstance(parent.law, Loop) and parent.children[0].goal.id == node.goal.id:
                    finding = dynamic.loop_finding(self, parent.goal, parent.law, law.expr)
            elif isinstance(law, Loop) and any(v.obligation.kind == "init" for v in bad):
                finding = dynamic.loop_finding(self, node.goal, law, None)
        except Exception:                               # a harness that does not elaborate must never hide the real verdict
            finding = None
        if finding is not None:
            for verdict in bad:
                if verdict.obligation.kind in ("term", "init"):
                    verdict.counterexample = finding.text()
                    break

    def apply(self, goal_id: int, law: Law, lemmas=()) -> Step:
        """Apply ``law`` at ``goal_id``. ``lemmas`` (``HelperLemma`` or their JSON) are proved first; accepted ones stay."""
        node = self.nodes.get(goal_id)
        if node is None:
            return Step(False, "unknown_goal", f"there is no goal {goal_id}")
        if node.law is not None:
            return Step(False, "unknown_goal", f"goal {goal_id} is already solved")
        try:
            helpers = [h if isinstance(h, HelperLemma) else HelperLemma.from_json(h) for h in lemmas]
            expansion = law.expand(node.goal, self._fresh)
        except IllFormed as error:
            return Step(False, "ill_formed", str(error))
        for helper in helpers:
            refused = self._admit(helper)
            if refused is not None:
                status = {"TIMEOUT": "timeout", "ILL_FORMED": "ill_formed"}.get(refused.status, "lemma_unproved")
                return Step(False, status, f"the helper lemma {helper.name} was not accepted", [refused])
        verdicts = [self._check(ob, f"obl{goal_id}_{k}") for k, ob in enumerate(expansion.obligations)]
        bad = [v for v in verdicts if not v.proved]
        if bad:
            status = {"ILL_FORMED": "ill_formed", "TIMEOUT": "timeout"}.get(bad[0].status, "unproved")
            if any(v.status == "ILL_FORMED" for v in bad):
                status = "ill_formed"
            elif status == "unproved" and self.counterexamples:
                self._run_the_loop(node, law, bad)
            return Step(False, status, f"the {law.kind} step is not accepted", verdicts)
        node.law, node.verdicts = law, verdicts
        node.children = [Node(g) for g in expansion.subgoals]
        for child in node.children:
            self.nodes[child.goal.id] = child
        return Step(True, "applied", "", verdicts, list(expansion.subgoals))

    def retract(self, goal_id: int) -> None:
        """Withdraw the law applied at ``goal_id`` and everything derived below it: the goal is open again."""
        node = self.nodes[goal_id]

        def drop(parent: Node):
            for child in parent.children:
                drop(child)
                self.nodes.pop(child.goal.id, None)
            parent.children = []
        drop(node)
        node.law, node.verdicts = None, []

    def apply_tree(self, tree: dict, goal_id: Optional[int] = None) -> List[Step]:
        """Apply a nested derivation ``{"law": ..., "children": [...]}`` from ``goal_id`` (default: the root), depth first.
        Stops at the first step Lean does not accept."""
        goal_id = goal_id if goal_id is not None else self.root.goal.id
        try:
            law = law_from_json(tree)
        except IllFormed as error:
            return [Step(False, "ill_formed", str(error))]
        step = self.apply(goal_id, law, tree.get("lemmas") or ())
        steps = [step]
        if not step.ok:
            return steps
        children = tree.get("children")
        if children is None:                              # no sub-derivation given: the sub-goals stay open
            return steps
        if len(children) > len(step.subgoals):
            steps.append(Step(False, "ill_formed", f"the {law.kind} law leaves {len(step.subgoals)} goals "
                                                   f"but {len(children)} sub-derivations were given"))
            return steps
        for goal, sub in zip(step.subgoals, children):
            steps += self.apply_tree(sub, goal.id)
            if not steps[-1].ok:
                break
        return steps

    def to_tree(self, node: Optional[Node] = None) -> dict:
        node = node or self.root
        if node.law is None:
            return {"law": None}
        return {**node.law.to_json(), "children": [self.to_tree(child) for child in node.children]}

    # --- the finished term ----------------------------------------------------------------------------------------

    def _render(self, node: Node, tactic: Optional[str] = None) -> Rendered:
        if node.law is None:
            raise ValueError(f"goal {node.goal.id} is not solved")
        tactic = tactic or self.tactic
        parts = [self._render(child, tactic) for child in node.children]
        return node.law.render(node.goal, [c.goal for c in node.children], parts, tactic)

    def source(self) -> str:
        """The Lean file: prelude, loop definitions, the derived subtype value, the plain function, its specification theorem."""
        task, goal = self.task, self.root.goal
        rendered = self._render(self.root, "refine_auto")
        params = goal.binders()
        call = goal.call()
        function = f"{task.name} {call}"
        statement = task.root_post.replace(HOLE, f"({function})")
        # the cascade is defined once as a tactic, so that each proof site in the file reads ``by refine_auto``
        macro = f'macro "refine_auto" : tactic => `(tactic| ({self.tactic}))\n'
        return "\n".join([
            self.lemmas, task.prelude, self._helper_text(), "", macro, *rendered.aux, "",
            f"set_option maxHeartbeats 1000000 in",
            f"def {task.name}_derived {params} : {goal.spec_type} :=",
            f"  {rendered.term}", "",
            f"def {task.name} {params} : {task.ret} := ({task.name}_derived {call}).val", "",
            f"theorem {task.name}_spec_satisfied {params} :",
            f"    {statement} := ({task.name}_derived {call}).property", "",
            f"#print axioms {task.name}_spec_satisfied", ""])

    def certify(self, run_tests: bool = True) -> Certificate:
        if not self.complete:
            return Certificate(False, [f"{len(self.open_goals())} goals are still open"])
        started = time.time()
        source = self.source()
        reply = self.lean.run(source, timeout=max(self.timeout, 240.0))
        certificate = Certificate(not reply.errors and not reply.timed_out, errors=reply.errors[:3])
        theorem = f"'{self.task.name}_spec_satisfied'"
        for info in reply.infos:
            if theorem not in info:
                continue
            found = PRINT_AXIOMS.search(info)
            if found:
                certificate.axioms = found.group(1)
            elif "does not depend on any axioms" in info:
                certificate.axioms = ""
        if reply.timed_out:
            certificate.errors = ["timeout"]
        if run_tests and certificate.compiles:
            tests = self.task.test_commands()
            certificate.tests = len(tests)
            ran = self.lean.run(source + "\n" + "\n".join(tests), timeout=max(self.timeout, 240.0))
            certificate.passed = sum(1 for info in ran.infos if info.strip() == "true")
        certificate.seconds = round(time.time() - started, 2)
        return certificate
