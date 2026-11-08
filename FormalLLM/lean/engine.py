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
import hashlib
import json
import os
import re
import time
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from FormalLLM.lean.laws import (Goal, HOLE, IllFormed, Law, Obligation, Rendered, RESULT, law_from_json, with_bound)


def _binder_names(binders: str) -> Optional[List[str]]:
    """The names bound by ``(a : A) (h : P a) ...``; ``None`` if there are implicit or instance binders."""
    names, depth, start = [], 0, None
    for k, ch in enumerate(binders):
        if ch in "{[" and depth == 0:
            return None
        if ch == "(":
            if depth == 0:
                start = k + 1
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                names += binders[start:k].split(":", 1)[0].split()
    return names
from FormalLLM.lean import cache, smallscope
from FormalLLM.lean.lemmas import EVAL_SET, LEMMAS, SIMP_SET
from FormalLLM.lean.session import LeanSession
from FormalLLM.lean.task import LeanTask

#: the library ``lib_chain`` chains over, as ``solve_by_elim`` arguments: the lemmas up to the task-family facts added from
#: 28 Oct (``filter_mergeSort_key`` on). With those (many hypotheses each) the search no longer fails fast but runs out of
#: heartbeats (he_009, he_010, he_022 regressed); ``lib_apply`` and the portfolio still use the whole library
_NAMES = __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES
LIBRARY = ", ".join(f"Refine.{n}" for n in _NAMES[:_NAMES.index("filter_mergeSort_key")])
#: lemmas ``grind`` refuses ("failed to find an usable pattern": an iff over a binder, a conclusion with no subterm to match).
#: One refused argument fails the whole ``grind [...]`` call, so ``lib_grind`` failed on every goal while they were listed.
#: It is not in the cascade: everything certified so far was certified without it, and running it on every goal that the
#: cascade fails made the runs several times slower and spent the heartbeats certificates need (he_010)
NO_GRIND_PATTERN = {
    "forall_mem_iff_idx", "exists_mem_iff_idx", "exists_le_succ", "forall_le_succ", "forall_mem_toList_iff_idx",
    "exists_mem_toList_iff_idx", "forall_mem_array_iff_idx", "exists_mem_array_iff_idx", "forall_mem_drop_iff",
    "exists_mem_drop_iff", "forall_mem_take_iff", "filter_pair_le", "ts_inner_init", "ts_outer_init", "ts_inner_step",
    "ts_inner_exit", "ts_outer_step", "ts_lex_all", "ts_pairwise_none", "mergeSort_key_le", "mergeSort_key_le_nat",
    "pairwise_mergeSort_key_le", "filter_mergeSort_key", "filter_mergeSort_key_int", "filter_mergeSort_key_nat",
    "filter_ne_append_filter_eq_perm", "pow_iff_of_factor", "mod_left_of_common_divisors", "mod_right_of_common_divisors",
    "le_of_common_divisors", "mergeSort_key_then_le",
    "foldl_pair_count", "foldl_pair_count_fst", "foldl_pair_count_snd"}
#: ... the rest, as ``grind`` arguments
LIBRARY_GRIND = ", ".join(f"Refine.{n}" for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES
                          if n not in NO_GRIND_PATTERN)
#: ``(apply L; all_goals first | assumption | (simp_all; done) | omega) | ...`` for every library lemma (fails fast on a mismatch)
LIBRARY_APPLY = "".join(f"(apply Refine.{n}; all_goals first | assumption | (simp_all; done) | omega) | "
                        for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES)
#: ... and side goals for ``grind`` too; a side goal over members (``∀ g ∈ l, P g``) whose facts the simp set turned into
#: the index form (``∀ k < l.length, P l[k]``) is bridged by naming the member's index (he_001)
LIBRARY_APPLY_GRIND = "".join(
    f"(apply Refine.{n}; all_goals first | assumption | (simp_all; done) | omega | grind | "
    f"(intro _ hmem; obtain ⟨_, _, rfl⟩ := List.getElem_of_mem hmem; grind)) | "
    for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES)


def make_cascade(extra_simp=(), task_defs=(), pre="True"):
    """The tactic that proves an obligation, and its *diagnosis* form (a part no tactic closes becomes ``sorry``, so that
    Lean reports its goal state). It reduces ``fun`` redexes and projections, splits conjunctions, then tries each tactic in
    turn. ``Refine.*`` are the lemmas of ``lemmas.py``; ``extra_simp`` are helper lemmas a step brought along."""
    simp = ", ".join([SIMP_SET, *extra_simp])
    # the task's own helper definitions (``fib4Spec``, ``isPal``...): unfold them one step and finish by arithmetic. Last, because
    # unfolding a recursive definition can hit Lean's recursion limit, which ``first`` cannot catch (he_046, he_063)
    defs = ", ".join(task_defs)
    defs_alt = (f" | (simp_all [{simp}, {defs}]; done) | (simp_all [{simp}, {defs}] <;> omega) | "
                f"(simp only [{defs}] at * <;> grind)") if task_defs else ""
    # helper lemmas are used three ways: as rewrite rules (above); by ``apply`` when the goal is one of their conclusions (the
    # hypotheses are then discharged by ``simp_all``); and by ``grind``, which instantiates them by pattern
    helpers = ""
    if extra_simp:
        names = ", ".join(extra_simp)
        # ``done``: ``simp_all`` succeeds without closing a goal, and ``first`` then takes this alternative: the proof ended
        # with "unsolved goals", which reads as an ill-formed step (he_012: five of o3-mini's loops refused that way)
        applied = " | ".join(f"(apply {n} <;> simp_all; done)" for n in extra_simp)
        helpers = f"{applied} | (grind [{names}]) | (simp_all [{simp}] <;> grind [{names}]) | "
    groups = _cascade_groups(simp, helpers, defs_alt, pre)
    tactic = ("(try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | "
              f"(simp_all [{simp}]; done) | (simp_all [{simp}]; omega) | (simp_all; omega) | "
              f"(simp_all [{simp}, Nat.mul_comm]; done) | (simp_all [{simp}, mul_assoc]; done) | "
              f"(split <;> simp_all [{simp}]; done) | "
              f"(split_ifs <;> simp_all [{simp}] <;> omega) | (simp_all [{simp}, Nat.mul_comm, Nat.mul_left_comm]; done) | "
              # a quantifier over members whose predicate mentions a loop variable (``∀ w ∈ words, f w ≤ f words[b]!``): turn it into
              # the index form the invariant uses, then let ``grind`` close it (``simp_all`` leaves it open: found on he_158)
              f"(rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | "
              + helpers +
              f"(norm_num; done) | (simp_all [{simp}]; norm_num; done) | "
              # a goal that is a library fact as stated (``he_034``'s was ``Refine.dedup_mergeSort_strict`` exactly): apply it
              + "lib_apply | " +
              # backward chaining over the whole library (the closest thing here to the paper's prover searching its
              # library): split the conjunctions, bring the bound variables in, and chain library lemmas and hypotheses.
              # grind alone failed on he_009 because it rewrites `take (i + 1)` away from the form the lemmas state
              # facts hidden in the precondition / in conjunctions (`h : f_precond a b` = `a > 0 ∧ b > 0`) are made usable:
              # unfold the precondition and split every conjunction hypothesis (he_013 needed `0 < a`)
              f"((try intros); (try unfold {pre} at *); (try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> "
              f"first | omega | lib_chain) | "
              # closed-form values: evaluate indices into constructions only (EVAL_SET), keep `take (i + 1)` and members as stated
              f"((try intros); (try simp_all only [{EVAL_SET}]); (repeat' apply And.intro) <;> (try intros) <;> "
              f"lib_chain) | "
              # lists built by appending (`acc ++ [d, x]`, the builder family): evaluate the index into the append / literal,
              # split the cases, and let grind finish on the goal as written. Not the full simplifier first: it turns
              # `acc[j]!` into `acc[j]` in the goal but not in the invariant, and grind then cannot connect them (he_005)
              f"((try intros); (try split_ifs) <;> (try simp only [Refine.getElem_bang_append, Refine.getElem_bang_cons, "
              f"Refine.getElem_bang_nil] at *) <;> (try split_ifs) <;> grind) | "
              # builder loops over a prefix (`acc = (l.take i).filterMap f`): one more element of the prefix, distribute the
              # map/filter over the append, substitute the invariant, split the match on `l[i]?` (he_022)
              "((try intros); (try casesm* _ ∧ _); (try simp only [Refine.take_succ_getElem?, List.filterMap_append, List.map_append, List.filter_append, List.flatMap_append] at *); (try subst_vars); (try split) <;> (simp_all; done)) | "
              f"nlinarith | (aesop; done) | decide{defs_alt})")
    diagnose = tactic[:-1] + " | sorry)"
    if extra_simp:
        use = lambda n: f"(apply {n}; all_goals first | done | assumption | (simp_all; done) | omega | grind)"
        whole = " | ".join(use(n) for n in extra_simp)
        # a step obligation is ``invariant' ∧ variant decreases``: apply the lemma to the part that is its conclusion
        both = " | ".join(f"(refine And.intro ?_ ?_ <;> first | {use(n)} | (dsimp only; omega) | omega)" for n in extra_simp)
        whole = whole + " | " + both
        groups = [f"first | {whole}"] + groups
        PORTFOLIO_CACHE[(tuple(extra_simp), defs, pre)] = groups
        return f"first | {whole} | ({tactic})", f"first | {whole} | ({diagnose})"
    PORTFOLIO_CACHE[(tuple(extra_simp), defs, pre)] = groups
    return tactic, diagnose


#: Lean's built-in hammer as a last stage of the prover (``Derivation._hammer_tactics``); FORMALLLM_HAMMER=0 turns it off
HAMMER = os.environ.get("FORMALLLM_HAMMER", "1") != "0"
#: the external-prover hammer (``refine_hammer``: premise selection -> Zipperposition -> Duper reconstruction), present
#: only when the session imports ``LeanEnv.Hammer``
ATP = "LeanEnv.Hammer" in os.environ.get("FORMALLLM_LEAN_IMPORTS", "")
#: the per-goal portfolio tries many slow alternatives (``try?``, Zipperposition) on each goal: it gets more time
PORTFOLIO_TIMEOUT = 600.0
#: what ``refine_portfolio`` logs for each goal it closes
PORTFOLIO_CLOSER = re.compile(r"refine_portfolio: (.+)$", re.S)


def heartbeats(proof: str, default: int) -> int:
    """The heartbeat limit of a theorem with this proof. ``refine_portfolio`` gives each alternative its own budget, but Lean
    keeps counting for the whole theorem, which then failed after every goal was closed (he_025, he_044): no limit there."""
    return 0 if "refine_portfolio" in proof else default

#: the cascade's alternatives as separate groups (see ``Derivation._portfolio``), filled by ``make_cascade``
PORTFOLIO_CACHE: Dict[tuple, List[str]] = {}


def _cascade_groups(simp: str, helpers: str, defs_alt: str, pre: str) -> List[str]:
    """The cascade's alternatives in groups, each a complete tactic of its own. A Lean resource limit (heartbeats, recursion
    depth) raised by one alternative is not caught by ``first``: it ends the whole cascade, and the alternatives after it
    never run (he_001, he_103: "deterministic timeout at whnf"). Run separately, a group that explodes cannot stop the others."""
    start = "(try dsimp only at *); (repeat' apply And.intro); all_goals (first | "
    lib_apply = "lib_apply"
    chunks = [
        f"omega | (simp_all [{simp}]; done) | (simp_all [{simp}]; omega) | (simp_all; omega) | (simp_all; done) | "
        f"(split_ifs <;> simp_all [{simp}] <;> omega) | (split <;> simp_all [{simp}]; done)",
        (helpers.rstrip(" |") if helpers else ""),
        lib_apply,
        f"((try intros); (try unfold {pre} at *); (try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> "
        f"first | omega | lib_chain) | "
        f"((try intros); (try simp_all only [{EVAL_SET}]); (repeat' apply And.intro) <;> (try intros) <;> "
        f"lib_chain)",
        f"((try intros); (try split_ifs) <;> (try simp only [Refine.getElem_bang_append, Refine.getElem_bang_cons, "
        f"Refine.getElem_bang_nil] at *) <;> (try split_ifs) <;> grind)",
        f"grind | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind)",
        # the library for grind: here and in ``refine_portfolio`` only, where it costs nothing to the goals the cascade
        # proves (he_010's loop exit: `grind` with the library, 3 s)
        f"lib_grind | (simp_all [{simp}] <;> lib_grind)",
        "((try intros); (try casesm* _ ∧ _); (try simp only [Refine.take_succ_getElem?, List.filterMap_append, List.map_append, List.filter_append, List.flatMap_append] at *); (try subst_vars); (try split) <;> (simp_all; done))",
        f"(norm_num; done) | (simp_all [{simp}]; norm_num; done) | nlinarith | (aesop; done) | decide",
        defs_alt.lstrip(" |"),
    ]
    return [start + c + ")" for c in chunks if c.strip()]


CASCADE, DIAGNOSE = make_cascade()
#: the library steps as named tactics, defined once. Spelling the 90-lemma library out in every alternative made the cascade
#: ~28k characters, and parsing it took Lean ~17 s per macro (twice per certificate): a full run would take hours longer
#: The library searches run within a heartbeat budget of their own: a search that runs out fails like any tactic, and
#: ``first`` goes on to the next alternative. Without it the declaration's limit is hit, which ``first`` cannot catch, and
#: the whole cascade fails (``lib_chain`` over the grown library took 40 s on he_009 and hid the alternative after it)
LIB_MACROS = ('open Lean Elab Tactic in\n'
              'elab "lib_budget " n:num ppSpace t:tactic : tactic => do\n'
              '  let ok ← tryCatchRuntimeEx\n'
              '    (do withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := n.getNat * 1000 * 1000 }) <|\n'
              '          evalTactic t\n'
              '        pure true)\n'
              '    (fun e => if e.isRuntime then pure false else throw e)\n'
              '  unless ok do throwError "lib_budget: the heartbeat budget ran out"\n'
              f'macro "lib_grind" : tactic => `(tactic| lib_budget 40 (grind [{LIBRARY_GRIND}]))\n'
              f'macro "lib_chain" : tactic => `(tactic| lib_budget 40 (solve_by_elim (maxDepth := 6) [{LIBRARY}]))\n'
              f'macro "lib_apply" : tactic => `(tactic| first | {LIBRARY_APPLY.rstrip(" |")})\n'
              # the library's rewrites, for ``refine_portfolio``'s ``unfold_local; (try lib_simp); lib_apply`` (he_033)
              f'macro "lib_simp" : tactic => `(tactic| simp_all [{SIMP_SET}])\n'
              # ``lib_apply`` whose side goals may also need ``grind`` (a hypothesis to project from under a binder: he_001)
              f'macro "lib_apply_grind" : tactic => `(tactic| first | {LIBRARY_APPLY_GRIND.rstrip(" |")})\n')
#: the library cascade as a named tactic in every task environment (see ``Derivation.__init__``)
AUTO_CLOSE = LIB_MACROS + f'macro "auto_close" : tactic => `(tactic| ({CASCADE}))\n'
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
        return f"set_option maxHeartbeats {heartbeats(self.proof, 400000)} in\ntheorem {self.name} : {self.statement} := {self.proof}\n"

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
RESOURCE_LIMIT = re.compile(r"maximum recursion depth|maximum number of heartbeats|deterministic\) timeout")


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
        # the common automation as a tactic, ``auto_close``, usable inside helper-lemma and sub-agent proofs: the model writes
        # the structure of a proof (cases, witnesses), the automation the routine parts (arithmetic, indexing, library facts)
        self.lemmas = lemmas + ("\n" + AUTO_CLOSE if lemmas is LEMMAS else "")
        self.helpers: List[HelperLemma] = []
        self.counterexamples, self.timeout = counterexamples, timeout
        self._next = 0
        root = Goal(self._fresh(), tuple((n, t) for n, t in task.params),
                    (("h_precond", f"{task.pre_name} {task.args}"),) if task.precond_arg else (), task.ret, task.root_post)
        self.nodes: Dict[int, Node] = {root.id: Node(root)}
        self.root = self.nodes[root.id]
        self._memo: Dict[str, Verdict] = {}
        self._env_id: Optional[int] = None
        self._env_restarts = -1
        self.lean_seconds = 0.0
        # where the Lean time goes, by phase (``phase``); written into every run row (``lspec_run.row_of``)
        self.timing: Dict[str, float] = defaultdict(float)
        self.counts: Dict[str, int] = defaultdict(int)
        self._phase = "cascade"

    @contextmanager
    def phase(self, name: str):
        """Attribute the Lean time of the commands run inside to ``name`` (``timing``, ``counts``)."""
        old, self._phase = self._phase, name
        try:
            yield
        finally:
            self._phase = old

    def _account(self, name: str, started: float) -> None:
        self.timing[name] += time.time() - started
        self.counts[name] += 1

    def _context_hash(self) -> str:
        """What every verdict in this derivation's environment depends on besides the obligation itself (``cache.py``)."""
        text = "\x00".join([self.lemmas, self.task.compat, self.task.prelude, self._helper_text()])
        return hashlib.sha256(text.encode("utf8")).hexdigest()

    @staticmethod
    def _normalise(source: str, name: str) -> str:
        """The command with its theorem name made neutral (goal ids differ between runs for the same obligation)."""
        return re.sub(r"\b" + re.escape(name) + r"\b", "OBLIGATION", source)

    def timing_report(self) -> dict:
        return {k: {"seconds": round(v, 1), "commands": self.counts[k]}
                for k, v in sorted(self.timing.items(), key=lambda kv: -kv[1])}

    def _fresh(self) -> int:
        self._next += 1
        return self._next

    @property
    def tactic(self) -> str:
        return self._tactic or make_cascade([h.name for h in self.helpers], self._task_defs(), self.task.pre_name)[0]

    @property
    def diagnose(self) -> str:
        return self._diagnose or make_cascade([h.name for h in self.helpers], self._task_defs(), self.task.pre_name)[1]

    def _task_defs(self) -> list:
        """Names of the helper functions the task's specification defines (not its pre/postcondition)."""
        import re as _re
        names = _re.findall(r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?def\s+([A-Za-z_][A-Za-z0-9_']*)", self.task.prelude)
        skip = {self.task.pre_name, self.task.post_name, "mkArray", "empty"}          # Verina compatibility shims
        return [n for n in dict.fromkeys(names) if n not in skip][:6]

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
            started = time.time()
            base = self._library_env()
            self._account("library_load", started)
            started = time.time()
            source = ("" if base is not None else self.lemmas + "\n") + self.task.prelude + "\n" + self._helper_text()
            reply, env = self._load_on(source, base, self._replay_timeout())
            self._account("env_load", started)
            if env is None and reply.timed_out:
                # a starved or bloated REPL times out on a load that normally takes seconds; the session restarted itself
                # on the timeout, so try once more on the fresh process (with more time) before calling it a failure
                base = self._library_env()
                source = ("" if base is not None else self.lemmas + "\n") + self.task.prelude + "\n" + self._helper_text()
                reply, env = self._load_on(source, base, max(300.0, self.lean.command_timeout * 2))
            if env is None:
                raise ValueError("the task's own definitions do not compile: " + (reply.errors or ["?"])[0][:300])
            self._env_id, self._env_restarts = env, self.lean.restarts
        return self._env_id

    def _library_env(self) -> Optional[int]:
        """The session's environment with the lemma library elaborated once (``LeanSession.library_env``); ``None``
        for a session without it, and the library text is then sent with the task as before."""
        library_env = getattr(self.lean, "library_env", None)
        return library_env(self.lemmas) if library_env is not None else None

    def _load_on(self, source: str, base: Optional[int], timeout: Optional[float]):
        return self.lean.load(source, timeout=timeout) if base is None else self.lean.load(source, timeout=timeout,
                                                                                            env=base)

    def _replay_timeout(self) -> Optional[float]:
        """Time to re-check the helper lemmas: ``refine_portfolio`` proofs replay their closers (``grind +suggestions``,
        ``try?``...), which can take minutes each (he_001: the 90 s limit cut a proof that had just been found)."""
        n = sum(1 for h in self.helpers if "refine_portfolio" in h.proof)
        return PORTFOLIO_TIMEOUT * n if n else None

    def _run(self, source: str, timeout: Optional[float] = None):
        started = time.time()
        env = self._environment()
        started = time.time()
        reply = self.lean.run(source, timeout=timeout or self.timeout, env=env)
        self.lean_seconds += time.time() - started
        self._account(self._phase, started)
        return reply

    def _witness_tactic(self, obligation: Obligation) -> Optional[str]:
        """An obligation about a postcondition that asks for a witness (``∃ i, ...``): the automation never chooses one,
        so try the context's number variables first (a loop very often computes exactly the index the specification
        asks for: he_012's ``∃ i, strings[i]! = s ∧ ...`` is the loop's ``b``). ``None`` when this does not apply."""
        if obligation.body is not None:
            return None
        post = self.task.post_name
        definition = self.task.prelude.split(f"def {post}", 1)
        if post not in obligation.statement or len(definition) < 2 or "∃" not in definition[1]:
            return None
        candidates = []
        depth, start = 0, None
        for k, ch in enumerate(obligation.binders):
            if ch == "(":
                if depth == 0:
                    start = k + 1
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and start is not None and ":" in obligation.binders[start:k]:
                    names, typ = obligation.binders[start:k].split(":", 1)
                    if typ.strip() in ("Nat", "ℕ", "Int", "ℤ"):
                        candidates += [n for n in names.split() if not n.startswith("h")]
        if not candidates:
            return None
        finish = ("(repeat' apply And.intro) <;> (first | omega | rfl | (simp_all; done) | "
                  "(rw [Refine.forall_mem_iff_idx]; intros; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (intros; grind))")
        tries = [f"((try unfold {post} at *); (try simp only [{post}] at *); refine ⟨{v}, ?_⟩; {finish})"
                 for v in candidates[-4:][::-1]]
        return "first | " + " | ".join(tries)

    def _cases_tactic(self, obligation: Obligation) -> Optional[str]:
        """A postcondition over inputs of a sum type (HumanEval's ``PyVal``, ``Option``, ``Bool``, or an ``inductive`` of the
        task): case-split those inputs, then simplify (he_092: ``cases x <;> cases y <;> cases z <;> simp``)."""
        if obligation.body is not None or self.task.post_name not in obligation.statement:
            return None
        inductives = set(re.findall(r"(?m)^\s*inductive\s+([A-Za-z_][A-Za-z0-9_']*)", self.task.prelude)) | {"PyVal", "Bool"}
        names = []
        depth, start = 0, None
        for k, ch in enumerate(obligation.binders):
            if ch == "(":
                if depth == 0:
                    start = k + 1
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and start is not None and ":" in obligation.binders[start:k]:
                    vs, typ = obligation.binders[start:k].split(":", 1)
                    head = typ.strip().split()[0] if typ.strip() else ""
                    if head in inductives or head == "Option":
                        names += [v for v in vs.split() if not v.startswith("h")]
        if not names or len(names) > 3:
            return None
        post = self.task.post_name
        split = " <;> ".join(f"cases {v}" for v in names)
        return (f"((try unfold {post} at *); {split} <;> (first | (simp_all; done) | (simp_all <;> omega) | (simp_all <;> grind) "
                f"| (decide) | grind))")

    def _prove_as_helper(self, obligation: Obligation, name: str, tactic: str) -> bool:
        """Prove the obligation with ``tactic`` in a command of its own; on success keep the proof as an automatic helper
        lemma, so that the final certificate (which re-runs only the common cascade, ``refine_auto``) closes this proof site
        by ``apply`` too."""
        names = _binder_names(obligation.binders)
        if names is None:
            return False
        portfolio = "refine_portfolio" in tactic
        source = obligation.source(f"{name}_alt", tactic)
        if portfolio:
            source = source.replace("set_option maxHeartbeats 200000 in", "set_option maxHeartbeats 0 in", 1)
        ckey = cache.key("helper", self._context_hash(), self._normalise(source, f"{name}_alt"))
        hit = cache.get(ckey)
        if hit is not None:
            self.counts["cache_hit"] += 1
            if not hit.get("ok"):
                return False
            return self._admit(HelperLemma(f"auto_{len(self.helpers)}_{name}"[:60], hit["statement"], hit["proof"])) is None
        reply = self._run(source, timeout=PORTFOLIO_TIMEOUT if portfolio else None)
        if reply.timed_out:
            return False
        if reply.errors or reply.goals:
            cache.put(ckey, {"ok": False})
            return False
        if portfolio:
            # replay only the alternatives that closed a goal (the lemma is re-proved on every reload and in the certificate)
            closers = list(dict.fromkeys(m.group(1).strip() for info in reply.infos
                                         for m in [PORTFOLIO_CLOSER.match(info.strip())] if m))
            replay = "refine_portfolio [" + ", ".join(json.dumps(c, ensure_ascii=False) for c in closers) + "]"
            tactic = tactic.replace("refine_portfolio", replay)
        statement = f"∀ {obligation.binders}, {obligation.statement}" if obligation.binders.strip() else obligation.statement
        intro = f"  intro {' '.join(names)}\n" if names else ""
        lemma = HelperLemma(f"auto_{len(self.helpers)}_{name}"[:60], statement,
                            f"by\n{intro}  {with_bound(tactic, obligation.bound)}")
        accepted = self._admit(lemma) is None
        if accepted:
            cache.put(ckey, {"ok": True, "statement": lemma.statement, "proof": lemma.proof})
        return accepted

    def _portfolio_prove(self, obligation: Obligation, name: str) -> bool:
        """The combined cascade died on a Lean resource limit: run its groups one by one (each its own command and budget).
        A group that proves the obligation becomes an automatic helper lemma, so that the final certificate closes this
        proof site by ``apply`` instead of re-running the cascade that exploded."""
        make_cascade([h.name for h in self.helpers], self._task_defs(), self.task.pre_name)
        groups = PORTFOLIO_CACHE.get((tuple(h.name for h in self.helpers), ", ".join(self._task_defs()), self.task.pre_name), [])
        return any(self._prove_as_helper(obligation, f"{name}_g{k}", group) for k, group in enumerate(groups))

    def _check(self, obligation: Obligation, name: str) -> Verdict:
        verdict = self._check_once(obligation, name)
        if verdict.status != "UNPROVED" or verdict.counterexample:
            return verdict                              # proved, ill-formed, or false: no prover can do more
        # tactics the common cascade does not contain (they depend on this obligation): each proof found becomes a helper
        specials = [t for t in (self._witness_tactic(obligation), self._cases_tactic(obligation)) if t]
        with self.phase("specials"):
            if any(self._prove_as_helper(obligation, f"{name}_s{k}", t) for k, t in enumerate(specials)):
                return Verdict(obligation, "PROVED", seconds=verdict.seconds)
        with self.phase("portfolio_groups"):
            if ("resource limit" in verdict.message or "proof failed" in verdict.message) and self._portfolio_prove(obligation, name):
                return Verdict(obligation, "PROVED", seconds=verdict.seconds)
        with self.phase("hammer"):
            if HAMMER and any(self._prove_as_helper(obligation, f"{name}_h{k}", t)
                              for k, t in enumerate(self._hammer_tactics(obligation))):
                return Verdict(obligation, "PROVED", seconds=verdict.seconds)
        return verdict

    def _hammer_tactics(self, obligation: Obligation) -> List[str]:
        """Lean's own hammer, the counterpart of the paper's CoqHammer: premise selection over all of Mathlib (Sine Qua Non,
        the selector of Isabelle's Sledgehammer, built into Lean 4.34) feeding ``grind`` / ``solve_by_elim``, plus ``exact?``
        and ``try?`` (Lean's portfolio of strategies). Like CoqHammer's provers, each covers goals the others miss, so they
        run as a portfolio of separate commands, each under its own heartbeat limit; a proof found becomes a helper lemma."""
        if obligation.body is not None:
            return []
        prep = (f"(try unfold {self.task.post_name} {self.task.pre_name} at *); (try dsimp only at *); (try intros); "
                f"(try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> ")
        if ATP:
            # each goal on its own, by the first of: the cascade, the generic closers, the library search, try?, the external
            # hammer (``refine_portfolio`` in ``LeanEnv/Hammer.lean``); each under its own heartbeat budget
            # (no second attempt without ``prep``: ``auto_close`` splits the goal itself, and a failing portfolio costs
            # minutes; he_020's inner-loop invariant spent 435 s + 508 s on the two attempts)
            return [prep + "refine_portfolio"]
        return [prep + "first | (solve_by_elim +suggestions) | exact? | (grind +suggestions) | (simp_all; grind +suggestions)",
                prep + "try?",
                "try?"]

    def _check_once(self, obligation: Obligation, name: str) -> Verdict:
        source = obligation.source(name, self.diagnose)
        if source in self._memo:
            return self._memo[source]
        ckey = cache.key("check", self._context_hash(), self._normalise(source, name))
        hit = cache.get(ckey)
        if hit is not None:
            self.counts["cache_hit"] += 1
            verdict = Verdict(obligation, hit["status"], hit.get("message", ""), hit.get("unsolved", []),
                              hit.get("counterexample"))
            self._memo[source] = verdict
            return verdict
        reply = self._run(source)
        if reply.timed_out:
            verdict = Verdict(obligation, "TIMEOUT", "Lean gave no answer within the time limit", seconds=reply.seconds)
        elif reply.errors and obligation.body is None and RESOURCE_LIMIT.search(reply.errors[0]) and self._elaborates(obligation):
            # a tactic of the cascade ran into a Lean limit (recursion depth, heartbeats): ``first`` cannot catch that, so it
            # surfaced as an error. The statement itself is well-formed, so this is "the automation did not prove it", not
            # "the step is ill-formed": the step stays repairable by a proof
            verdict = Verdict(obligation, "UNPROVED", "the automation hit a Lean resource limit (" +
                              reply.errors[0].splitlines()[0][:120] + "); the statement itself is well-formed",
                              seconds=reply.seconds)
        elif reply.errors and obligation.body is None and self._elaborates(obligation):
            # any other error of the cascade on a statement that type-checks is a failed proof, not an ill-formed step (an
            # alternative that succeeded without closing its goal ended in "unsolved goals": he_012)
            verdict = Verdict(obligation, "UNPROVED", "the automation's proof failed (" +
                              reply.errors[0].splitlines()[0][:120] + "); the statement itself is well-formed",
                              seconds=reply.seconds)
        elif reply.errors:
            verdict = Verdict(obligation, "ILL_FORMED", reply.errors[0][:600], seconds=reply.seconds)
        elif reply.goals:
            verdict = Verdict(obligation, "UNPROVED", "no tactic of the cascade closes this", unsolved=reply.goals,
                              seconds=reply.seconds)
            if self.counterexamples:
                verdict.counterexample = self._counterexample(obligation, name)
        else:
            verdict = Verdict(obligation, "PROVED", seconds=reply.seconds)
        if verdict.status == "UNPROVED" and self.counterexamples and not verdict.counterexample:
            verdict.counterexample = self._small_scope(obligation)
        self._memo[source] = verdict
        if verdict.status != "TIMEOUT" and self.counterexamples:
            # (without the counter-example search a verdict lacks its counter-example: not stored, so that a later run
            # with the search still gets one)
            cache.put(ckey, {"status": verdict.status, "message": verdict.message, "unsolved": verdict.unsolved,
                             "counterexample": verdict.counterexample})
        return verdict

    def _elaborates(self, obligation: Obligation) -> bool:
        """The obligation's statement type-checks (its proof aside)."""
        with self.phase("elaborates"):
            reply = self._run(f"example {obligation.binders} :\n    {obligation.statement} := by\n  sorry\n")
        return not reply.timed_out and not reply.errors

    def _counterexample(self, obligation: Obligation, name: str) -> Optional[str]:
        source = (TESTING + f"theorem {name}_cex {obligation.binders} :\n    {obligation.statement} := by\n"
                  f"  (try dsimp only at *); plausible {PLAUSIBLE_CONFIG}\n")
        with self.phase("plausible"):
            reply = self._run(source)
        return reply.counterexample

    def _small_scope(self, obligation: Obligation) -> Optional[str]:
        """Every combination of small values (``smallscope.py``): the falsifying one, as the counter-example text."""
        source = smallscope.falsifier(obligation.binders, obligation.statement)
        if source is None:
            return None
        with self.phase("smallscope"):
            reply = self._run(source, timeout=60.0)
        if reply.timed_out or reply.errors:
            return None
        found = smallscope.parse("\n".join(reply.infos))
        return f"the statement is false for {found}" if found else None

    def _admit(self, lemma: HelperLemma) -> Optional[Verdict]:
        """Have Lean prove a helper lemma; ``None`` when it is accepted (and now part of the environment)."""
        if any(h.name == lemma.name for h in self.helpers):
            return Verdict(Obligation("lemma", f"helper lemma {lemma.name}", "", lemma.statement), "ILL_FORMED",
                           f"a helper lemma named {lemma.name} already exists")
        obligation = Obligation("lemma", f"helper lemma {lemma.name}", "", lemma.statement)
        with self.phase("admit_" + self._phase):
            reply = self._run(lemma.source(), timeout=PORTFOLIO_TIMEOUT if "refine_portfolio" in lemma.proof else None)
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
            with self.phase("dynamic"):
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
        if bad and all(v.obligation.kind == "exit" and v.status == "UNPROVED" for v in bad):
            # a loop whose invariant does not bound the guard's variable: retry with the bound added (``Loop.bounded``)
            bounded = getattr(law, "bounded", lambda: None)()
            if bounded is not None:
                step = self.apply(goal_id, bounded)
                if step.ok:
                    return step
        if bad:
            status ={"ILL_FORMED": "ill_formed", "TIMEOUT": "timeout"}.get(bad[0].status, "unproved")
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

    def source(self, library: bool = True) -> str:
        """The Lean file: prelude, loop definitions, the derived subtype value, the plain function, its specification
        theorem. ``library=False`` leaves out the lemma library, for elaborating on top of an environment that has it."""
        task, goal = self.task, self.root.goal
        rendered = self._render(self.root, "refine_auto")
        params = goal.binders()
        call = goal.call()
        function = f"{task.name} {call}"
        statement = task.root_post.replace(HOLE, f"({function})")
        # the cascade is defined once as a tactic, so that each proof site in the file reads ``by refine_auto``
        macro = f'macro "refine_auto" : tactic => `(tactic| ({self.tactic}))\n'
        return "\n".join([
            *([self.lemmas] if library else []), task.prelude, self._helper_text(), "", macro, *rendered.aux, "",
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
        # on top of the session's library environment (the library was proved when it was loaded; ``#print axioms``
        # still follows every dependency), so the ~140k-character library is not elaborated twice more per task; the
        # self-contained file, library included, is what ``source()`` returns and what the fresh-process check compiles
        base = self._library_env()
        source = self.source(library=base is None)
        limit = max(self.timeout, 240.0, self._replay_timeout() or 0)

        def run(text: str):
            if base is None:
                return self.lean.run(text, timeout=limit)
            return self.lean.run(text, timeout=limit, env=base)
        # one command: the term, then the tests (an earlier version compiled the whole file a second time for the tests);
        # messages are told apart by line, so a test that does not run never counts against the term
        prefix = self.task.compat + "\n" if self.task.compat else ""     # the dataset's prelude (e.g. the witness search)
        tests = self.task.test_commands() if run_tests else []
        body = prefix + source
        reply = run(body + ("\n" + "\n".join(tests) if tests else ""))
        self._account("certify", started)
        first_test = body.count("\n") + 2 if tests else 10 ** 9
        errors = [e for e, line in zip(reply.errors, reply.error_lines or [0] * len(reply.errors)) if line < first_test]
        infos = [(i, line) for i, line in zip(reply.infos, reply.info_lines or [0] * len(reply.infos))]
        certificate = Certificate(not errors and not reply.timed_out, errors=errors[:3])
        theorem = f"'{self.task.name}_spec_satisfied'"
        for info in [i for i, line in infos if line < first_test]:
            if theorem not in info:
                continue
            found = PRINT_AXIOMS.search(info)
            if found:
                certificate.axioms = found.group(1)
            elif "does not depend on any axioms" in info:
                certificate.axioms = ""
        if reply.timed_out:
            certificate.errors = ["timeout"]
        if tests and certificate.compiles:
            certificate.tests = len(tests)
            certificate.passed = sum(1 for i, line in infos if line >= first_test and i.strip() == "true")
        certificate.seconds = round(time.time() - started, 2)
        return certificate
