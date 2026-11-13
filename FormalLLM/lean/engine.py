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
from typing import Dict, List, Optional, Tuple

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

#: rewrites to the forms the shape tactics are written for, tried first inside those tactics only (never in the shared simp
#: sets, so a proof that works on the written form is never disturbed): ``max(l)`` written as ``l.max?.get!``, the first of a
#: filter as ``(l.filter p)[0]!``, a search as a fold with ``||`` (gpt-5.4-mini on Verina, 2026-11-13)
NORMALIZE = ("(try simp only [Refine.max_get_eq_foldl_int, Refine.max_get_eq_foldl_nat, Refine.min_get_eq_foldl_int, "
             "Refine.min_get_eq_foldl_nat, Refine.filter_getElem_zero_eq_find, Refine.filter_head_eq_find, "
             "Refine.foldl_or_eq_any, Refine.foldl_and_eq_all, Refine.foldl_decide_or_eq_any, Bool.false_or, "
             "Bool.true_and, Nat.add_sub_cancel_left] at *); ")
#: the same, with the maximum of a list of naturals folded from 0 (``foldl max 0``, the form brute-force specs state)
NORMALIZE_ZERO = NORMALIZE.replace("Refine.max_get_eq_foldl_nat", "Refine.max_get_eq_foldl_zero_nat")

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
    "le_of_common_divisors", "mergeSort_key_then_le", "mergeSort_key_then_not_lt", "mergeSort_key_then_le_prop",
    "mergeSort_key_then_not_lt_prop",
    "foldl_pair_count", "foldl_pair_count_fst", "foldl_pair_count_snd"}
#: ... the rest, as ``grind`` arguments
LIBRARY_GRIND = ", ".join(f"Refine.{n}" for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES
                          if n not in NO_GRIND_PATTERN)
#: ``(apply L; all_goals first | assumption | (simp_all; done) | omega | decide) | ...`` for every library lemma (fails fast
#: on a mismatch; ``decide`` for side goals about the task's constant lists, he_148's ``solarPlanets.length ≤ 8``, under a
#: budget: a ``decide`` that runs out of heartbeats is not caught by ``first`` and would end the whole cascade)
LIBRARY_APPLY = "".join(f"(apply Refine.{n}; all_goals first | assumption | (simp_all; done) | omega | lib_budget 5 decide) | "
                        for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES)
#: ... and side goals for ``grind`` too; a side goal over members (``∀ g ∈ l, P g``) whose facts the simp set turned into
#: the index form (``∀ k < l.length, P l[k]``) is bridged by naming the member's index (he_001)
LIBRARY_APPLY_GRIND = "".join(
    f"(apply Refine.{n}; all_goals first | assumption | (simp_all; done) | omega | grind | "
    f"(intro _ hmem; obtain ⟨_, _, rfl⟩ := List.getElem_of_mem hmem; grind)) | "
    for n in __import__("FormalLLM.lean.lemmas", fromlist=["NAMES"]).NAMES)


def _balanced(text: str, start: int) -> int:
    """Index just past the parenthesis group opening at ``text[start] == "("``."""
    depth = 0
    for k in range(start, len(text)):
        depth += {"(": 1, ")": -1}.get(text[k], 0)
        if depth == 0:
            return k + 1
    return len(text)


def _exit_guard(binders: str) -> Optional[Tuple[str, str, str]]:
    """A loop exit's negated guard of the form ``(hNg : ¬ ((A) ∧ (¬ (B))))``: ``(name, A, B)``, else None."""
    m = re.search(r"\((h\d+g) : ¬ \(", binders)
    if not m:
        return None
    inner_start = m.end() - 1
    inner = binders[inner_start + 1:_balanced(binders, inner_start) - 1].strip()
    if not inner.startswith("("):
        return None
    a_end = _balanced(inner, 0)
    rest = inner[a_end:].strip()
    if not rest.startswith("∧ (¬ (") or not rest.endswith("))"):
        return None
    return m.group(1), inner[1:a_end - 1], rest[len("∧ (¬ ("):-2]


def _nat_subtractions(text: str) -> List[Tuple[str, str]]:
    """Every ``(L) - (R)`` with both sides parenthesised, innermost first: ``[(L, R), ...]``."""
    out = []
    for m in re.finditer(r"\) - \(", text):
        k, depth = m.start(), 0                       # the group closing at ``text[k]``
        while k >= 0:
            depth += {")": 1, "(": -1}.get(text[k], 0)
            if depth == 0:
                break
            k -= 1
        right_start = m.end() - 1
        right_end = _balanced(text, right_start)
        if k >= 0:
            out.append((text[k + 1:m.start()], text[right_start + 1:right_end - 1]))
    return sorted(set(out), key=lambda p: len(p[0]) + len(p[1]))


def _binder_types(binders: str) -> List[Tuple[str, str]]:
    """``(a b : List Int) (s : String)`` -> ``[("a", "List Int"), ("b", "List Int"), ("s", "String")]``."""
    out, depth, start = [], 0, None
    for k, ch in enumerate(binders):
        if ch == "(":
            if depth == 0:
                start = k + 1
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None and ":" in binders[start:k]:
                names, typ = binders[start:k].split(":", 1)
                out += [(n, typ.strip()) for n in names.split() if not n.startswith("h")]
    return out


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


#: ``wit_search``: an existential goal (also nested, under ``∧``, either side of ``∨``) by trying witnesses: the local variables of the
#: right type (the goal's context: the witnesses of the hypotheses, once unpacked), their successors, and the numerals 0,
#: 1, 2; each choice is finished by ``assumption``, ``omega`` or a budgeted ``grind`` (a heartbeat timeout is not an
#: error a ``try`` catches: one runaway ``grind`` ended the whole search on he_020's inner loop). The cascade never
#: chooses a witness (he_020's loop init: ``∃ b < 2, ∃ a < b, ...`` holds for b = 1, a = 0). Under a heartbeat budget of
#: its own: unbounded, it ran 970 s on he_001's loop exit
WIT_SEARCH = r"""open Lean Elab Tactic Meta in
partial def Refine.witSearch (depth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let tgt ← whnfR (← instantiateMVars (← goal.getType))
  if tgt.isForall then
    let (_, g) ← goal.intro1
    setGoals [g]
    Refine.witSearch depth
    return
  if tgt.isAppOfArity ``And 2 then
    for g in ← goal.apply (mkConst ``And.intro []) do
      setGoals [g]
      Refine.witSearch depth
    return
  if depth > 0 && tgt.isAppOfArity ``Or 2 then
    for side in [``Or.inl, ``Or.inr] do
      let s ← saveState
      try
        for g in ← goal.apply (mkConst side []) do
          setGoals [g]
          Refine.witSearch (depth - 1)
        return
      catch _ => s.restore
  if depth > 0 && tgt.isAppOfArity ``Exists 2 then
    let ty ← instantiateMVars (tgt.getArg! 0)
    let mut cands : Array Expr := #[]
    for d in (← goal.getDecl).lctx do
      if !d.isImplementationDetail && (← isDefEq d.type ty) then
        cands := cands.push d.toExpr
    -- the goal's own terms of that type (he_148: the witness is `solarPlanets.idxOf planet1`)
    let found ← IO.mkRef (#[] : Array Expr)
    forEachExpr' (← instantiateMVars (tgt.getArg! 1)) fun x => do
      let subs ← found.get
      if subs.size < 6 && !x.hasLooseBVars && !x.isFVar && !x.isRawNatLit && x.isApp && !x.isAppOf ``OfNat.ofNat
          && !(subs.contains x) then
        if ← isDefEq (← inferType x) ty then
          found.modify (·.push x)
      return true
    cands := cands ++ (← found.get)
    if ← isDefEq ty (mkConst ``Nat) then
      for c in cands do
        cands := cands.push (mkNatAdd c (mkNatLit 1))
      cands := cands ++ #[mkNatLit 0, mkNatLit 1, mkNatLit 2]
    if ← isDefEq ty (mkConst ``Int) then
      cands := cands ++ #[toExpr (0 : Int), toExpr (1 : Int)]
    for c in cands do
      let s ← saveState
      try
        setGoals [← goal.existsIntro c]
        Refine.witSearch (depth - 1)
        return
      catch _ => s.restore
    throwError "wit_search: no witness found"
  setGoals [goal]
  evalTactic (← `(tactic| first | assumption | omega | (intros; omega) | rfl | lib_budget 5 decide | lib_budget 20 grind |
    lib_apply))

open Lean Elab Tactic in
elab "wit_search_core" : tactic => Refine.witSearch 4
macro "wit_search" : tactic => `(tactic| lib_budget 400 wit_search_core)
"""
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
              f'macro "lib_apply_grind" : tactic => `(tactic| first | {LIBRARY_APPLY_GRIND.rstrip(" |")})\n'
              + WIT_SEARCH)
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
#: small inputs only (``maxSize``, default 100): a counter-example is almost always small, and a specification that
#: enumerates subsequences (Verina's LCS / LIS) took 1000-2100 s and pushed the machine into swap at the default size
PLAUSIBLE_CONFIG = "(config := { randomSeed := some 20261008, numInst := 200, maxSize := 10 })"
#: the counter-example search's own time limit (it is feedback, not proof)
PLAUSIBLE_TIMEOUT = 30.0
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
        self._libeq_tried = False

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

    def _shape_tactics(self, obligation: Obligation) -> List[str]:
        """Tactics for shapes the common cascade handles badly, each tried as a command of its own (a proof found becomes a
        helper lemma, as for the other specials). They start by unfolding only the pre/postcondition: the cascade's
        ``dsimp``/``simp_all`` first unfolds ``String.mk``, ``Nat.toDigits`` and the task's functions too, and on closed
        forms that ran out of heartbeats before any library lemma was tried (he_038, he_044, he_079, he_087)."""
        if obligation.body is not None:
            return []
        post, pre = self.task.post_name, self.task.pre_name
        start = (f"(try unfold {post} {pre} at *); (try simp only [{post}] at *); "
                 "(try simp only [Refine.string_toList_mk, Refine.string_length_mk] at *); ")
        tactics = []
        # the same value written another way (gpt-5.4-mini, Verina 2026-11-13): ``max(l)`` is ``l.max?.get!``, the first of a
        # filter is ``(l.filter p)[0]!``, a search is a fold with ``||``; rewritten to the forms the tactics below are written
        # for (``foldl max (headD 0)``, ``find? … |>.getD``, ``any``), and the gates read the statement as rewritten
        stmt = obligation.statement
        if ".max?.get!" in stmt or ".min?.get!" in stmt:
            stmt += " foldl max"
        if ".filter" in stmt and ("[0]!" in stmt or ".head!" in stmt):
            stmt += " find? getD"
        if "foldl" in stmt and ("∨" in stmt or "||" in stmt) and "List.range" in stmt:
            stmt += " .any"
        definition = self.task.prelude.split(f"def {post}", 1)
        if "∃" in obligation.statement or (len(definition) > 1 and "∃" in definition[1].split("\ndef ", 1)[0]):
            # (a result chosen by ``if``, a postcondition ``A ∨ ∃ i, ...``: he_135's loop exit)
            tactics.append(start + "(try intros); (try split_ifs) <;> (try casesm* _ ∧ _, Exists _) <;> wit_search")
            # ... with the disjunctions of the hypotheses split too (he_118: the invariant is "none so far, or the last one
            # found is c")
            tactics.append(start + "(try intros); (try split_ifs) <;> (try casesm* _ ∧ _, Exists _, _ ∨ _) <;> "
                                   "(try subst_vars) <;> wit_search")
        # members to indices, in the hypotheses too, then grind (he_090: the hypotheses state the loop's facts by index,
        # the postcondition by members; the cascade turns only the goal)
        tactics.append(start + "simp only [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.mem_iff_idx] at *; "
                               "first | grind | wit_search")
        # the conjuncts of a closed form one by one, by a library lemma, by evaluation once the variables are
        # substituted, or by grind with the library
        tactics.append(start + "(repeat' apply And.intro) <;> (try intros) <;> (try casesm* _ ∧ _) <;> "
                               "first | lib_apply | (simp_all; done) | (subst_vars; decide) | "
                               "(subst_vars; simp; done) | (subst_vars; simp; rfl) | (subst_vars; simp; decide) | lib_grind")
        # ... or evaluated whole by the construction lemmas (``EVAL_SET``: ``Nat.toDigits 2 v`` is a binary numeral of v,
        # he_079, he_084, he_103), the rest by grind with the library
        tactics.append(start + f"simp [{EVAL_SET}] <;> first | done | lib_grind")
        # characters: a map over a string whose letters all satisfy a class (lowercase, uppercase, digit) is decided letter
        # by letter on the class's finitely many codes (he_050: shifting by 21 then by 5 is the identity on 'a'..'z').
        # ``lower_cases`` & co. are not in the library lists: their conclusion ``P c`` would unify with any goal
        cases = ("first | assumption | exact Refine.lower_cases _ (by decide) | exact Refine.upper_cases _ (by decide) | "
                 "exact Refine.digit_cases _ (by decide)")
        tactics.append(start + "(repeat' apply And.intro) <;> (try simp only [List.map_map]) <;> first | "
                               f"(apply Refine.map_eq_self_of_all <;> {cases}) | (apply Refine.all_map_of_all <;> {cases})")
        # the task's own non-recursive helpers unfolded, the constructions rewritten by the library (``EVAL_SET``), then
        # each conjunct by a library lemma or the whole cascade (he_033: ``atMod 3`` of the result is the sorted list
        # by ``gather_scatter3``, and a sorted list is sorted)
        plain = [f for f in self._task_defs() if f not in self._recursive_defs()]
        if plain:
            tactics.append(f"simp only [{post}, {', '.join(plain)}, List.length_map, List.length_range] at *; "
                           f"(try simp only [{EVAL_SET}]); (repeat' apply And.intro) <;> (try intros) <;> "
                           "first | trivial | lib_apply | auto_close")
        # the maximum of a list the postcondition builds by brute force (all subarrays, subsequences, common subsequences):
        # ``L.foldl max d`` is a member of L and bounds it once L is not empty (``maxlist_*``); L is not empty by its length,
        # by a witness (the empty subarray, the empty subsequence, a one-element list after splitting an input list), or
        # after a split on the input's ``match`` (Verina advanced_2, 3, 4, 28, 29, 43, 45, 46, 75)
        if "foldl max" in stmt:
            tactics.append(self._max_tactic(obligation, plain))
            if ".max?.get!" in obligation.statement:
                tactics.append(self._max_tactic(obligation, plain, NORMALIZE_ZERO))
        # a bounded search for a witness, ``(range (n + 1)).any p`` against the postcondition's ``∃ m, p m``: equivalent once
        # every witness is at most n (``any_range_iff``), a power ``b ^ m`` is at least m and a digit past the number's
        # length is 0 (Verina advanced_14, advanced_20)
        if "List.range" in stmt and ".any" in stmt:
            bound = ("intro m hm; simp only [beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at hm; first "
                     "| (rw [hm]; apply Refine.le_pow_self'; norm_num; done) | (rw [← hm]; apply Refine.le_pow_self'; norm_num; done) "
                     "| (by_contra hc; rw [Refine.div_pow_eq_zero_of_lt] at hm <;> first | (simp at hm; done) | omega | (norm_num; done)) "
                     "| omega")
            tactics.append(f"unfold {post}; (try unfold {pre} at *); {NORMALIZE}"
                           "(try simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]); "
                           f"rw [Refine.any_range_iff]; all_goals first | ({bound}) | exact Iff.rfl | (simp; done) | "
                           "(simp [eq_comm]; done)")
        split = "(try intros); (repeat' apply And.intro) <;> (try intros) <;> (try casesm* _ ∧ _)"
        # a polynomial identity over Nat with a subtraction (``2 * i - 1``): split the variable at 0, then the subtraction
        # normalises away and ``nlinarith`` closes the step (Verina basic_7: a sum of odd squares)
        if " - " in obligation.statement and "*" in obligation.statement:
            for var, typ in _binder_types(obligation.binders)[:3]:
                if typ in ("Nat", "ℕ"):
                    tactics.append(start + f"{split} <;> first | omega | (rcases {var} with _ | {var} <;> "
                                           "norm_num [Nat.mul_add, Nat.add_mul] at * <;> nlinarith)")
        # an ordering kept as a ``Pairwise`` fact implies a weaker ``Pairwise`` (Verina basic_89: ``a`` before ``b`` in the
        # input, so also when ``a`` is before ``b`` in the result)
        if "Pairwise" in obligation.statement or "Pairwise" in self.task.prelude:
            tactics.append(start + f"{split} <;> first | (apply List.Pairwise.imp _ ‹List.Pairwise _ _›; intros; assumption) "
                                   "| grind")
        # conjunctions split through their implications, arrays to indices, then by arithmetic: Nat casts into Int
        # (Verina basic_81: ``x / y * y + x % y = x`` and ``x % y < y`` as Int), a position and what follows it in an
        # array (basic_46)
        through = (f"(try unfold {post} {pre} at *); (try simp only [{post}] at *); "
                   "(repeat' (first | apply And.intro | intro)) <;> (try casesm* _ ∧ _)")
        tactics.append(through + " <;> (try simp only [Int.ofNat_eq_coe, List.all_eq_true, decide_eq_true_eq, "
                       "Refine.forall_mem_drop_toList_iff, Refine.forall_mem_toList_iff_idx] at *) <;> first "
                       "| (exfalso; contradiction) | omega | positivity | (norm_cast; apply Nat.div_add_mod') "
                       "| (norm_cast; apply Nat.mod_lt; omega) | grind")
        # ... with ``all``/``any`` over arrays and ranges as quantifiers, and an index split at 0 for a fact stated at ``i + 1``
        # (Verina basic_108: every prefix sum is ``s[0] = 0`` or ``s[i + 1]``, which is not negative)
        tactics.append(through + " <;> (try simp only [Array.all_eq_true, List.any_eq_false, List.mem_range, decide_eq_true_eq, "
                       "not_lt, ge_iff_le] at *) <;> first | omega | grind "
                       "| (intro k hk; rw [← getElem!_pos _ k hk]; rcases k with _ | k <;> grind)")
        # a result found by ``find?`` with a default: split on what ``find?`` returns; found, the element satisfies the
        # predicate and is in the list, not found, no element does; then counting facts (Verina advanced_11: a majority
        # leaves every other value at most half, ``filter_le_half_or_eq``; advanced_54: a
        # list of n distinct values up to n misses exactly one of 0..n, ``range_not_subset``, ``missing_unique``; advanced_55:
        # the most frequent element, the largest count is attained, ``not_all_ne_max_dec``)
        if "find?" in stmt and "getD" in stmt:
            # two different values cannot both occur more than half the time (advanced_35 written as ``filter(p)[0]``):
            # the found value's count and the other one's, over each list the obligation binds
            pair = "".join(f"| (have hc1 := of_decide_eq_true hfs; have hc2 := Refine.count_pair_le {v} _ _ ‹_ ≠ _›; omega) "
                           for v, typ in _binder_types(obligation.binders) if typ.startswith("List"))
            tactics.append(f"unfold {post}; {NORMALIZE}(try simp only [{pre}] at h_precond); (try dsimp only); (try intros); "
                           "unfold Option.getD; split <;> (try simp only [List.find?_eq_none] at *) <;> "
                           "(try (have hfs := List.find?_some ‹List.find? _ _ = some _›; "
                           "have hfm := List.mem_of_find?_eq_some ‹List.find? _ _ = some _›)) <;> "
                           "(try simp only [decide_eq_true_eq, List.all_eq_true, not_lt] at *) <;> (try casesm* _ ∧ _) <;> "
                           "(repeat' (first | apply And.intro | intro)) <;> first | (exfalso; contradiction) | assumption "
                           "| omega | (left; assumption) | (exact Refine.filter_le_half_or_eq _ _ _ ‹_›) "
                           "| (right; exact ⟨‹_›, fun _ _ => Refine.filter_le_half_or_eq _ _ _ ‹_›⟩) "
                           "| (exfalso; exact Refine.range_not_subset _ ‹_›) "
                           "| (apply Refine.missing_unique _ _ _ _ hfm hfs <;> assumption) "
                           "| (exfalso; exact Refine.not_all_ne_max_dec _ _ ‹_› ‹_›) "
                           "| (simp only [List.all_eq_true, decide_eq_true_eq]; intro x hx; rw [of_decide_eq_true hfs]; "
                           "apply Refine.le_foldl_max; exact List.mem_map_of_mem hx) "
                           "| (simp only [of_decide_eq_true hfs]; rw [List.head?_filter]; assumption) "
                           + pair + "| (simp; done) | grind")
        # ``(l.find? p).getD d`` as the witness of a ``bind`` whose property is ``x ∈ l ∧ p x``, under a hypothesis that some
        # element satisfies ``p``: found, it is in the list and satisfies ``p``; not found contradicts the hypothesis (Verina
        # advanced_11: the majority element named before it is returned)
        if "find?" in stmt and "getD" in stmt:
            tactics.append("(try beta_reduce); (try intros); unfold Option.getD; split <;> "
                           "(try simp only [List.find?_eq_none] at *) <;> "
                           "(try (have hfs := List.find?_some ‹List.find? _ _ = some _›; "
                           "have hfm := List.mem_of_find?_eq_some ‹List.find? _ _ = some _›)) <;> "
                           "(try simp only [decide_eq_true_eq] at *) <;> first | exact ⟨hfm, hfs⟩ | exact hfs | exact hfm "
                           "| (exfalso; obtain ⟨_, hx, hp⟩ := ‹∃ _ ∈ _, _›; exact absurd hp (by simpa using ‹∀ _ ∈ _, _› _ hx)) "
                           "| grind")
        # the longest list with a property, ``(L.map List.length).foldl max 0`` cast to Int: the empty list is in ``L`` (by
        # induction along the postcondition's own ``let rec`` generator, e.g. all subsequences), so the maximum is attained
        # and bounds every length (``maxlen_spec``) (Verina advanced_24: longest increasing subsequence)
        if "foldl max 0" in stmt and "List.length" in stmt:
            recs = [f"{post}.{r}" for r in re.findall(r"let rec (\w+)", definition[1].split("\ndef ", 1)[0])] \
                if len(definition) > 1 else []
            rec_simp = ", ".join(recs)
            member = "".join(f"| (simp only [List.mem_filter]; refine ⟨?_, by simp [{rec_simp}]⟩; induction {v} <;> "
                             f"simp_all [{rec_simp}]) " for v, typ in _binder_types(obligation.binders)
                             if typ.startswith("List") and recs)
            tactics.append(f"unfold {post}; (try unfold {pre} at *); (try dsimp only); "
                           "(try simp only [Nat.cast_inj, Nat.cast_le]); refine Refine.maxlen_spec _ ?_; "
                           f"first | (simp; done) {member}")
        # a search that stops at the first ``r`` where a property holds (the invariant: no ``r' < r`` has it; the guard:
        # ``r < bound ∧ ¬ P r``): on exit ``P r`` holds, at the bound by the precondition (``take`` of the whole list); a
        # positive ``r`` is minimal by the invariant, ``r = 0`` leaves a target range empty (Verina advanced_52)
        if obligation.kind == "exit":
            guard = _exit_guard(obligation.binders)
            result = re.search(rf"{re.escape(post)} .*\((\w+)\) h_precond\s*$", obligation.statement)
            if guard and result:
                g, a, b = guard
                r = result.group(1)
                nats = "".join(f"| (cases {v} with | zero => rfl | succ {v} => exfalso; simp only [List.take_zero, "
                               f"List.all_eq_true, List.elem_nil] at hB; exact absurd (hB 1 (by simp)) (by simp)) "
                               for v, typ in _binder_types(obligation.binders) if typ in ("Nat", "ℕ") and v != r)
                tactics.append(f"unfold {post}; (try unfold {pre} at h_precond); (try dsimp only at *); "
                               f"have hB : {b} := by\n"
                               f"    by_cases hA : {a}\n"
                               f"    · exact Classical.byContradiction (fun hc => {g} ⟨hA, hc⟩)\n"
                               "    · first | (rw [List.take_of_length_le (by simp; omega)]; simp only [List.all_eq_true, "
                               "List.elem_eq_mem, decide_eq_true_eq, List.mem_reverse] at h_precond ⊢; first | exact h_precond "
                               "| grind) | grind\n"
                               f"  (try casesm* _ ∧ _); refine ⟨hB, ?_⟩; split\n"
                               "  · first | (apply ‹∀ _, _ < _ → _›; omega) | grind\n"
                               f"  · rw [show {r} = 0 by omega] at hB; first | rfl | (simp_all; done) {nats}")
        libeq_all = [h.name for h in self.helpers if h.name.startswith("auto_libeq_")]
        libeq_simp = "".join(f"{n}, " for n in libeq_all)
        pre_text = self.task.prelude.split(f"def {pre}", 1)
        pre_text = pre_text[1].split("\ndef ", 1)[0] if len(pre_text) > 1 else ""
        lists = [v for v, typ in _binder_types(obligation.binders) if typ.startswith("List")]
        # the one element occurring once, found by ``find?``, when the precondition says the list of counts has exactly
        # one 1 and every count is 1 or 2: it is unique (``count_one_unique``), so every other element occurs twice, and
        # it exists (``count_one_exists``) (Verina advanced_1: the single number)
        if "find?" in stmt and "getD" in stmt and ".count 1" in pre_text:
            tactics.append(
                f"unfold {post}; unfold {pre} at h_precond; (try dsimp only at *); "
                f"(try simp only [{libeq_simp}Refine.filter_eq_length_count] at *)\n"
                "  obtain ⟨hall, hone⟩ := h_precond\n"
                "  simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp, "
                "forall_apply_eq_imp_iff₂] at hall\n"
                "  unfold Option.getD; split\n"
                "  · rename_i r hf\n"
                "    have hfs := List.find?_some hf\n"
                "    have hfm := List.mem_of_find?_eq_some hf\n"
                "    simp only [decide_eq_true_eq] at hfs\n"
                "    (repeat' apply And.intro) <;> first | exact List.length_pos_of_mem hfm | exact hfs | (intro x hx; "
                "by_cases hxr : x = r; exact Or.inl hxr; right; rcases hall x hx with h1 | h2; "
                "exact absurd (Refine.count_one_unique _ hone _ _ h1 hfs) hxr; exact h2)\n"
                "  · rename_i hf; exfalso; rw [List.find?_eq_none] at hf\n"
                "    obtain ⟨x, hx, hc⟩ := Refine.count_one_exists _ hone\n"
                "    exact absurd hc (by simpa using hf x hx)")
        # the element minimising a key among those with a property, ``match l.filter p with | [] => none | b :: t =>
        # some ((b :: t).foldl argmin b)``: none, nothing has the property (no duplicates: ``nodup_iff_count_le_one``);
        # some, the fold's facts (``foldl_argmin_facts``) for the members of the filter (Verina advanced_12: the first
        # duplicate, by the index of its second occurrence)
        argmin = re.search(r"fun (\w+) (\w+) => if \((.+?) \2\) < \((.+?) \1\) then \2 else \1", obligation.statement)
        if argmin and argmin.group(3) == argmin.group(4) and "match" in obligation.statement and lists:
            key, l = argmin.group(3), lists[0]
            tactics.append(
                "split\n"
                f"  · rename_i hF; unfold {post}; rw [List.filter_eq_nil_iff] at hF; rw [List.nodup_iff_count_le_one]\n"
                f"    intro a; by_cases ha : a ∈ {l}\n"
                "    · have := hF a ha; simp at this; omega\n"
                "    · simp [List.count_eq_zero_of_not_mem ha]\n"
                f"  · rename_i b t hF; unfold {post}\n"
                f"    obtain ⟨h1, h2⟩ := Refine.foldl_argmin_facts ({key}) (b :: t) b\n"
                f"    have hsub : ∀ z, z ∈ b :: t ↔ z ∈ {l} ∧ {l}.count z > 1 := by intro z; rw [← hF]; simp\n"
                "    refine ⟨((hsub _).mp (by simp only [List.mem_cons] at h1 ⊢; tauto)).2, ?_⟩\n"
                "    simp only [List.all_eq_true, decide_eq_true_eq]; intro y hy\n"
                f"    by_cases hc : {l}.count y = 1\n"
                "    · exact Or.inl hc\n"
                f"    · right; apply h2; have : {l}.count y > 1 := by have := List.count_pos_iff.mpr hy; omega\n"
                "      exact List.mem_cons_of_mem _ ((hsub y).mpr ⟨hy, this⟩)")
        # a list split by a predicate and its negation, ``l.filter p ++ l.filter q`` (Verina advanced_56: move the zeroes
        # to the end): the kept order is a sublist, the tail after ``dropWhile p`` is the ``q`` part, counts and lengths add
        if "++" in obligation.statement and obligation.statement.count(".filter") >= 2 and lists:
            tactics.append(
                f"unfold {post}; (try simp only [{', '.join(libeq_all) or 'List.length_append'}] at *)\n"
                "  (repeat' apply And.intro) <;> first\n"
                "    | exact List.sublist_append_left _ _\n"
                "    | (rw [List.dropWhile_append_of_pos]; (simp only [List.all_eq_true, decide_eq_true_eq]; intro x hx; "
                "have := (List.dropWhile_sublist _).subset hx; simpa using (List.mem_filter.mp this).2); "
                "(intro a ha; simpa using (List.mem_filter.mp ha).2))\n"
                "    | (rw [List.count_append]; (conv_rhs => rw [List.count_eq_zero.mpr (by simp), List.count_filter (by simp)]); "
                "simp)\n"
                "    | (simp [List.count_append, List.count_filter]; done)\n"
                "    | (simp only [List.length_append]; grind [List.length_eq_length_filter_add])")
        # the first ``k`` of the distinct elements sorted by a key, descending (Verina advanced_76: the k most frequent):
        # distinct (``nodup_eraseDups'``), members of the input, every left-out element's key at most every kept one's
        # (``take_desc_cover``), ordered by the key (``pairwise_mergeSort_key_ge_nat``, indices for ``zipIdx``)
        sortkey = re.search(r"(\w+)\.eraseDups\.mergeSort \(fun (\w+) (\w+) => decide \(\((.+?) \3\) ≤ \((.+?) \2\)\)\)",
                            obligation.statement)
        if sortkey and sortkey.group(4) == sortkey.group(5) and ".take" in obligation.statement:
            l, key = sortkey.group(1), sortkey.group(4)
            takek = re.search(r"\.take (\w+)", obligation.statement)
            takek = takek.group(1) if takek else "_"
            srt = f"{l}.eraseDups.mergeSort (fun x y => decide (({key} y) ≤ ({key} x)))"
            tactics.append(
                f"unfold {post}; (try unfold {pre} at h_precond)\n"
                f"  have hS := Refine.pairwise_mergeSort_key_ge_nat (fun z => {key} z) {l}.eraseDups\n"
                f"  have hnd : {l}.eraseDups.Nodup := Refine.nodup_eraseDups' {l}\n"
                f"  have hmem : ∀ x, x ∈ {srt} ↔ x ∈ {l} := fun x => by rw [Refine.mem_mergeSort']; exact List.mem_eraseDups\n"
                "  (repeat' apply And.intro) <;> first\n"
                "    | (simp only [List.length_take, List.length_mergeSort]; omega)\n"
                "    | (simp only [List.all_eq_true, decide_eq_true_eq]; intro x hx; exact (hmem x).mp (List.mem_of_mem_take hx))\n"
                "    | exact ((List.mergeSort_perm _ _).nodup_iff.mpr hnd).sublist (List.take_sublist _ _)\n"
                "    | (simp only [List.all_eq_true, decide_eq_true_eq]; intro x hx y hy\n"
                "       exact Refine.take_desc_cover _ _ hS _ x y hx ((hmem y).mpr hy))\n"
                "    | (rw [Refine.pairwise_zipIdx_iff]; intro i j hij hj; dsimp only; intro _\n"
                f"       have hP := hS.sublist (List.take_sublist {takek} _)\n"
                "       rw [List.pairwise_iff_getElem] at hP\n"
                "       have := hP i j (by omega) hj hij\n"
                "       rw [getElem!_pos _ i (by omega), getElem!_pos _ j hj]; exact this)")
        # ... the same search returning ``if A then r else -1`` (the guard ``A ∧ ¬ P r``): inside the bound ``P r`` holds and
        # no earlier start has it (the invariant), at the bound none has (Verina advanced_8: the gas-station start)
        if obligation.kind == "exit":
            guard = _exit_guard(obligation.binders)
            if guard and f"(if {guard[1]} then" in obligation.statement:
                g, a, b = guard
                prior = ("(simp only [List.all_eq_true, List.mem_range, Int.toNat_natCast]; intro k hk; "
                         "have := ‹∀ _, _ < _ → _› k (by omega); simpa using this)")
                tactics.append(
                    f"unfold {post}; (try unfold {pre} at h_precond); (try dsimp only); (try casesm* _ ∧ _)\n"
                    f"  by_cases hA : {a}\n"
                    f"  · have hB := Classical.byContradiction (fun hc => {g} ⟨hA, hc⟩)\n"
                    "    simp only [hA, if_true]\n"
                    "    (repeat' (first | apply And.intro | intro)) <;> first | omega | (simpa using hB) | "
                    f"{prior} | grind\n"
                    "  · simp only [hA, if_false]\n"
                    f"    (repeat' (first | apply And.intro | intro)) <;> first | omega | {prior} | grind")
        # "some pair of members is related" computed as ``l.any (fun x => l.any (fun y => R x y))``, against a spec "pairwise
        # unrelated → false, some pair related → true": a related pair contradicts ``Pairwise`` when ``R`` is symmetric
        # and irreflexive, both by unfolding ``R`` to arithmetic (Verina advanced_13: intersecting chords)
        pairany = re.search(r"\.any \(fun (\w+) => \w+\.any \(fun (\w+) => ([\w.]+) \1 \2\)\)", obligation.statement)
        if pairany and "Pairwise" in (definition[1] if len(definition) > 1 else ""):
            rel = pairany.group(3)
            unf = f"simp only [{rel}, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, " \
                  "Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]"
            tactics.append(
                f"unfold {post}; (try dsimp only)\n"
                "  refine ⟨?_, id⟩\n"
                "  intro hP hR\n"
                "  simp only [List.any_eq_true] at hR\n"
                "  obtain ⟨x, hx, y, hy, hxy⟩ := hR\n"
                f"  have hsym : Std.Symm (fun x y => (!{rel} x y) = true) := ⟨fun a b h => by {unf} at *; omega⟩\n"
                "  by_cases he : x = y\n"
                f"  · subst he; {unf} at hxy; omega\n"
                "  · have := hP.forall hx hy he; simp [hxy] at this")
        # a sum kept by the postcondition's own ``let rec f (i : Nat) (acc : Int)`` (``if i >= n then acc else f (i + 1)
        # (acc + w i)``) of terms ``max 0 _``: it is never negative, by induction on ``n - i`` (Verina advanced_62: trapped
        # rain water)
        body = definition[1].split("\ndef ", 1)[0] if len(definition) > 1 else ""
        for rec, bound in re.findall(r"let rec (\w+) \(i : Nat\) \(acc : Int\) : Int :=\s*if i >= (\S+) then acc", body):
            if f"{post}.{rec}" in obligation.statement and "max 0" in obligation.statement:
                f = f"{post}.{rec}"
                args = re.search(rf"{re.escape(f)} (\w+) ", obligation.statement)
                pre_args = f"{args.group(1)} " if args and args.group(1) not in ("i", "acc") and "(" not in args.group(1) else ""
                tactics.append(
                    f"unfold {post}\n"
                    f"  have key : ∀ (W : Nat → Int), (∀ i, W i ≥ 0) → ∀ n i (acc : Int), {bound} - i = n → acc ≥ 0 →\n"
                    f"      {f} {pre_args}W i acc ≥ 0 := by\n"
                    "    intro W hW n; induction n with\n"
                    f"    | zero => intro i acc h hacc; unfold {f}; rw [if_pos (by omega)]; exact hacc\n"
                    "    | succ n ih =>\n"
                    f"      intro i acc h hacc; unfold {f}; split\n"
                    "      · exact hacc\n"
                    "      · exact ih (i + 1) _ (by omega) (by have := hW i; omega)\n"
                    "  (repeat' apply And.intro) <;> (try split) <;> first | omega | rfl | (simp_all; done) "
                    "| exact key _ (fun i => le_max_left _ _) _ 0 0 rfl (le_refl _)")
        # a number written back as its digits, ``if n = 0 then [0] else Nat.digits 10 n``, the inputs read by the task's
        # digit fold (= ``Nat.ofDigits 10``, ``_library_equations``): the digits read back to ``n``, are below 10, the last
        # is not 0; at 0, an input whose value is 0 and whose last digit is not 0 cannot exist (Verina advanced_5)
        if "Nat.digits 10" in obligation.statement and libeq_all:
            zero = "".join(f"| (rcases ‹_ ∨ {v} = [0]› with h | h; (exfalso; exact h (Refine.ofDigits_eq_zero_all 10 {v} "
                           f"(by norm_num) (by omega) _ (Refine.getLast_bang_mem {v} (List.ne_nil_of_length_pos ‹{v}.length > 0›)))); "
                           "exact h) " for v in lists)
            tactics.append(
                f"unfold {post}; unfold {pre} at h_precond; (try simp only [{', '.join(libeq_all)}] at *); "
                "(try casesm* _ ∧ _)\n"
                "  split\n"
                "  · rename_i hs\n"
                "    (repeat' (first | apply And.intro | apply Or.inr)) <;> first | rfl | (simp [Nat.ofDigits]; omega) "
                f"| (simp; done) {zero}\n"
                "  · rename_i hs\n"
                "    (repeat' apply And.intro) <;> first | exact Nat.ofDigits_digits 10 _ "
                "| (intro d hd; exact Nat.digits_lt_base (by norm_num) hd) "
                "| exact Or.inl (Refine.digits_getLast_bang_ne_zero 10 _ (by norm_num) hs)")
        # a polynomial with Nat subtractions in a loop invariant (``7 + 24 i³ - 12 i² - 14 i``): each subtraction never
        # truncates (proved for every k, inner ones first, by cases on k and nlinarith), instantiated at the loop
        # variable and its successor; then ``zify`` with those facts turns the step into an Int identity for nlinarith
        # (Verina basic_43: the sum of fourth powers of odd numbers)
        subs = _nat_subtractions(obligation.binders + " " + obligation.statement) if obligation.kind != "exit" else []
        nat_vars = [v for v, typ in _binder_types(obligation.binders) if typ in ("Nat", "ℕ")]
        loop_vars = [v for v in nat_vars if any(re.search(rf"\b{v}\b", l + r) for l, r in subs)]
        if subs and "^" in obligation.statement and len(loop_vars) == 1 and len(subs) <= 4:
            v = loop_vars[0]
            lines, facts = [], []
            for k, (l, r) in enumerate(subs):
                lk, rk = (re.sub(rf"\b{v}\b", "k", x) for x in (l, r))
                prev = "".join(f"have p{j} := nsub{j} k; " for j in range(k))
                zprev = ", ".join(f"p{j}" for j in range(k))
                zprev = f" [{zprev}]" if zprev else ""
                hints = ("sq_nonneg ((k : Int)), sq_nonneg ((k : Int) + 1), mul_nonneg (Int.natCast_nonneg k) "
                         "(sq_nonneg ((k : Int)))")
                lines.append(f"  have nsub{k} : ∀ k : Nat, {rk} ≤ {lk} := fun k => by first | omega "
                             f"| ({prev}rcases k with _ | k <;> [simp; (first | nlinarith [sq_nonneg k, pow_pos (Nat.succ_pos k) 3] "
                             f"| (zify{zprev}; push_cast; nlinarith [{hints}]) | (zify{zprev} at *; push_cast at *; "
                             f"nlinarith [{hints}]))])")
                facts += [f"b{k}", f"c{k}"]
                lines.append(f"  have b{k} := nsub{k} {v}; have c{k} := nsub{k} ({v} + 1)")
            tactics.append("(try beta_reduce); (try simp only [] at *); (try casesm* _ ∧ _)\n" + "\n".join(lines) + "\n"
                           f"  (repeat' apply And.intro) <;> first | omega | (zify [{', '.join(facts)}] at *; push_cast at *; "
                           "nlinarith)")
        # a search step: the invariant "no ``r' < r`` has the property" extends to ``r + 1`` by the guard ``¬ P r``
        # (Verina advanced_52, advanced_8: the loop's step)
        if obligation.kind != "exit" and re.search(r"∀ ([\w']+), \(\1 < \w+\) →", obligation.statement):
            tactics.append("(try beta_reduce); (try casesm* _ ∧ _); (repeat' (first | apply And.intro | intro)) <;> first "
                           "| omega | (rcases Nat.lt_succ_iff_lt_or_eq.mp ‹_ < _ + 1› with h | h <;> "
                           "[exact ‹∀ _, _ < _ → _› _ h ‹_›; (subst h; contradiction)])")
        # a value known by a hypothesis to occur more than half the time (a `bind` or a `cases` on it): every other value
        # occurs at most half the time (Verina advanced_11 when the result is named, not found by ``find?``)
        if "filter" in stmt + self.task.prelude and "/ 2" in stmt + self.task.prelude:
            tactics.append(f"unfold {post}; (try simp only [{pre}] at h_precond); (try dsimp only); (try intros); "
                           "(repeat' (first | apply And.intro | intro)) <;> (try simp only [decide_eq_true_eq, "
                           "List.all_eq_true, not_lt, Bool.decide_or, Bool.or_eq_true] at *) <;> (try casesm* _ ∧ _) <;> "
                           "first | (exfalso; contradiction) | assumption | omega "
                           "| (right; exact ⟨‹_›, fun _ _ => Refine.filter_le_half_or_eq _ _ _ ‹_›⟩) "
                           "| (exact ⟨‹_›, fun _ _ => Refine.filter_le_half_or_eq _ _ _ ‹_›⟩) "
                           "| (exact fun _ _ => Refine.filter_le_half_or_eq _ _ _ ‹_›)")
        # the precondition unfolded by name (``unfold post pre at *`` stops at the first name it cannot unfold), members of
        # arrays and lists as indices, the task's plain helpers unfolded, then grind (Verina basic_24: the precondition
        # has an even element, so a scan that stops at the first non-odd one stops inside the array)
        unfold_plain = f", {', '.join(plain)}" if plain else ""
        tactics.append(f"(try beta_reduce); (try unfold {post} at *); (try simp only [{pre}] at h_precond); "
                       "(try simp only [Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, "
                       f"Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx{unfold_plain}] at *); grind")
        # an index taken modulo the length (``(a % len).toNat``): it is in bounds when the list is not empty, so ``getD``
        # and ``[_]?`` at it are the element (Verina basic_39: rotate right)
        if "toNat" in obligation.statement and "%" in obligation.statement:
            tactics.append(f"unfold {post}; (try simp only [{pre}] at *); (repeat' (first | apply And.intro | intro)) <;> "
                           "simp_all [Refine.getD_emod, Refine.getElem?_emod]")
        # a result sorted with mergeSort: sorted (``pairwise_mergeSort_le_int``), without repeats when its input was
        # deduplicated, and membership through the sort, ``dedup``, ``++`` and ``filter`` (Verina basic_22: the sorted
        # symmetric difference of two arrays)
        if "mergeSort" in obligation.statement:
            tactics.append(f"unfold {post}; (try simp only [{pre}] at *); (try simp only [Refine.array_any_eq_iff_mem{unfold_plain}] at *); "
                           "(repeat' apply And.intro) <;> first | (simpa using Refine.pairwise_mergeSort_le_int _) "
                           "| (exact (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup _)) "
                           "| (simp only [Array.all_eq_true_iff_forall_mem, List.all_eq_true, List.mem_toArray, List.mem_mergeSort, "
                           "List.mem_dedup, List.mem_append, List.mem_filter]; intro x hx; simp only [Array.mem_def] at *; "
                           "(try split) <;> simp at hx ⊢ <;> tauto)")
        binders = _binder_types(obligation.binders)
        # an array result kept as ``acc.toList = <list>``: every array taken apart into its list, so the facts are about
        # lists (Verina basic_60: the exit of a filter loop, ``take i`` of the whole input is the input)
        arrays = [v for v, typ in binders if typ.startswith("Array")]
        if arrays and 0 < len(arrays) <= 3:
            parts = " <;> ".join(f"rcases {v} with ⟨{v}⟩" for v in arrays)
            tactics.append(through + f" <;> {parts} <;> simp_all <;> (try simp (disch := omega) only [List.take_of_length_le]) "
                           "<;> first | done | exact List.filter_sublist | rw [List.countP_eq_length_filter] | grind")
        # a loop with a Bool flag ("found"): split on the flag; found, the invariant's facts are the postcondition (with
        # ``ts_lex_all`` for "no earlier pair"), not found, no pair exists (``ts_pairwise_none``), or the precondition
        # says one does (``pairsum_exists_of_count``) (Verina advanced_78, 79: two-sum)
        flags = [v for v, typ in binders if typ == "Bool"]
        if flags and obligation.kind == "exit":
            tactics.append(f"(try unfold {post} at *); (try simp only [{pre}] at h_precond); (try dsimp only at *); "
                           f"(try intros); (try casesm* _ ∧ _); cases {flags[0]} <;> simp only [Bool.false_eq_true, "
                           "↓reduceIte, true_implies, false_implies, forall_const, if_true, if_false, Bool.true_eq_false, "
                           f"reduceCtorEq, and_true, not_and, not_lt] at * <;> (try simp only [{post}]) <;> "
                           "(try casesm* _ ∧ _) <;> first | (exact ⟨‹_›, ‹_›, ‹_›, Refine.ts_lex_all _ _ _ _ ‹_› ‹_› ‹_›⟩) "
                           "| (exact ⟨‹_›, by omega, ‹_›, ‹_›⟩) | (apply Refine.ts_pairwise_none; intro i2 j2 hij hj; grind) "
                           "| (exfalso; obtain ⟨i2, j2, h1, h2, h3⟩ := Refine.pairsum_exists_of_count _ _ ‹_›; grind)")
        # a loop step with a Bool flag: split the step's ``if``, case on the flag, then the invariant's facts for the
        # first ``i`` elements and the new one (Verina basic_40: second smallest, ``found`` once a larger value is seen)
        if flags and obligation.kind != "exit" and "if " in obligation.statement:
            tactics.append(f"(try beta_reduce); (try simp only [{pre}] at h_precond); (try casesm* _ ∧ _); (try split) <;> "
                           f"cases {flags[0]} <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_implies, "
                           "true_implies, forall_const, true_and, and_true, false_or, true_or, or_false, imp_false, not_true, "
                           "not_false_eq_true] at * <;> grind")
        # a search loop whose invariant is "found here, or not in the first i rows": on exit each side is one side of
        # the postcondition; not found, the loop ran to the end, so no row holds the key (``all_all_of_bang``)
        # (Verina basic_90: search in a sorted 2-D array)
        if obligation.kind == "exit" and "∨" in obligation.binders:
            tactics.append(f"unfold {post}; (try simp only [{pre}] at h_precond); (try dsimp only); (try casesm* _ ∧ _); "
                           "rcases ‹_ ∨ _› with h | h <;> [left; right] <;> (try casesm* _ ∧ _) <;> first "
                           "| (exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩) | (exact ⟨‹_›, ‹_›, ‹_›⟩) | (exact ⟨‹_›, ‹_›⟩) "
                           "| (refine ⟨‹_›, ‹_›, ?_⟩; apply Refine.all_all_of_bang _ _ _ _ ‹_›; omega) | grind")
        # a 2-D array whose precondition says every row has the same size (``Pairwise (·.size = ·.size)``): every row has
        # the size of row 0 (``rect_row_size``), then the result's ``if`` split (Verina basic_90: the inner loop's exit)
        if "Array (Array" in obligation.binders:
            tactics.append(f"(try beta_reduce); (try simp only [{pre}] at h_precond); (try casesm* _ ∧ _); "
                           "have hrect := Refine.rect_row_size _ ‹_›; (try split) <;> first | (left; grind) | (right; grind) | grind")
        # the result is the maximum of a brute-force list (``(range n).flatMap (fun i => (range m).map (f i))``,
        # ``foldl max 0``) and the spec quantifies over ``zipIdx``: indices for ``zipIdx``, the maximum named ``R`` with
        # its facts (an upper bound of every ``f i j``, and 0 or attained: ``foldl_max_pairs``), then each part
        # (Verina advanced_42: best stock profit)
        if ("foldl max 0" in obligation.statement or ".max?.get!" in obligation.statement) and "flatMap" in obligation.statement:
            tactics.append(f"unfold {post}; (try simp only [{pre}] at *); {NORMALIZE_ZERO}(try simp only [Refine.pairwise_zipIdx_iff, "
                           "Refine.zipIdx_all_iff, Refine.zipIdx_any_iff, decide_eq_true_eq]); "
                           "generalize hR : List.foldl max 0 _ = R; (first "
                           "| (have hf := Refine.foldl_max_pairs _ _ _ _ hR; beta_reduce at hf) "
                           "| (have hf := Refine.foldl_max_filter_pairs _ _ _ _ hR; beta_reduce at hf) "
                           "| (have hf := Refine.foldl_max_facts_eq _ _ hR; simp only [List.mem_flatMap, List.mem_map, "
                           "List.mem_range, List.mem_filter] at hf)); "
                           "clear hR; obtain ⟨hA, hB⟩ := hf; (repeat' apply And.intro) <;> (try apply Iff.intro) <;> "
                           "(try intros) <;> (try rcases hA with hA | ⟨i0, hi0, j0, hj0, hx0⟩) <;> (try split at hx0) <;> grind")
        # a bounded search for a power, ``(range (n.toNat + 1)).any (fun x => b ^ x = n ...)``, after the task's own power
        # function is rewritten to ``^`` (``_library_equations``): a witness is below ``n`` since ``x < b ^ x``
        # (Verina advanced_23: a power of two)
        libeq = [h.name for h in self.helpers if h.name.startswith("auto_libeq_")]
        if libeq and ".any" in stmt and "List.range" in stmt:
            bound = " | ".join(f"(have := Refine.int_lt_pow {b} x (by norm_num); omega)" for b in (2, 3, 4, 10))
            tactics.append(f"unfold {post}; (try unfold {pre} at *); {NORMALIZE}(try simp only [{', '.join(libeq)}] at *); split <;> "
                           "rename_i h <;> simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢ <;> first "
                           "| (obtain ⟨x, _, hx⟩ := h; exact ⟨x, hx⟩) "
                           f"| (rintro ⟨x, hx, hn⟩; apply h; refine ⟨x, ?_, hx, hn⟩; first | {bound}) "
                           # the condition split between the search and a case's hypothesis (``n > 0`` known from a
                           # ``cases`` step, the search testing only ``pow 2 x = n``: gpt-5.4-mini, advanced_23)
                           "| (obtain ⟨x, _, hx⟩ := h; exact ⟨x, by first | exact hx | (exact ⟨hx, by omega⟩) | simp_all⟩) "
                           f"| (rintro ⟨x, hx⟩; apply h; (try obtain ⟨hx, _⟩ := hx); exact ⟨x, by first | {bound}, "
                           "by first | exact hx | simp_all⟩)")
        # induction along a recursive function of the task (he_038: ``encodeGroups`` applied three times is the identity)
        for f in self._recursive_defs():
            for var, typ in _binder_types(obligation.binders):
                if typ.startswith("List"):
                    tactics.append(start + f"induction {var} using {f}.induct <;> first | (simp_all [{f}]; done) | grind [{f}]")
                elif typ == "String":
                    tactics.append(start + f"generalize {var}.toList = l at *; induction l using {f}.induct <;> "
                                           f"first | (simp_all [{f}]; done) | grind [{f}]")
        return tactics

    def _max_tactic(self, obligation: Obligation, plain: List[str], normalize: str = NORMALIZE) -> str:
        post, pre = self.task.post_name, self.task.pre_name
        simp = f"simp [{', '.join(plain)}]" if plain else "simp"
        lists = [v for v, typ in _binder_types(obligation.binders) if typ.startswith("List")]
        cases = "".join(f" | (cases {v} <;> simp_all <;> wit_search)" for v in lists)
        # each alternative ends in ``done``: one that leaves goals would otherwise win the ``first``
        nonempty = ("first | (apply List.ne_nil_of_length_pos; simp; done) | (simp; done) "
                    "| (intro hnil; have := congrArg List.length hnil; simp at this; done) "
                    f"| ({simp} <;> first | (refine ⟨[], ?_⟩; simp [Refine.allsub_nil_mem_arr, Refine.allsub_nil_mem]; done) "
                    f"| wit_search{cases})")
        member = f"first | (simp; done) | ({simp} <;> wit_search)"
        apply = (f"first | (refine Refine.maxlist_int _ ?_; {nonempty}) | (refine Refine.maxlist_nat _ ?_; {nonempty}) "
                 f"| (refine Refine.maxlist_int_any _ ?_; {nonempty}) | (refine Refine.maxlen_spec _ ?_; {member})")
        return (f"unfold {post}; (try unfold {pre} at *); {normalize}(try dsimp only at *); (try intros); (try split) <;> "
                f"(try (exfalso; simp_all; done)) <;> first | ({apply}) | ((repeat' apply And.intro) <;> (try intros) <;> "
                f"first | (exfalso; contradiction) | ({apply}) | (left; exact ⟨‹_›, rfl⟩) | (right; refine ⟨‹_›, ?_⟩; {apply}))")

    def _library_equations(self) -> bool:
        """Recognise the task's own recursive functions as library functions, by their signature, and admit the equation as
        a helper lemma when Lean proves it: ``f (b : T) (e : Nat) : T`` as ``b ^ e`` (Verina advanced_23), ``f : List Nat →
        Nat`` as ``Nat.ofDigits`` in base 10 or 2 (advanced_5), ``f (x : T) (l : List T) : List T`` with a ``let rec aux``
        as ``l.filter (· = x)`` (advanced_1). True when an equation was added."""
        prelude = self.task.prelude
        recursive = set(self._recursive_defs())
        found = False
        heads = list(re.finditer(r"(?m)^def\s+([A-Za-z_][\w']*)\s*((?:\([^()]*\)\s*)*):\s*([^\n]+?)\s*(?::=|$)", prelude))
        for m in heads:
            name, binders, ret = m.group(1), m.group(2), m.group(3).strip()
            body = re.split(r"(?m)^\S", prelude[m.end():], maxsplit=1)[0]
            params = [(n, typ.strip()) for names, typ in re.findall(r"\(([^():]+):\s*([^()]+)\)", binders)
                      for n in names.split()]
            types = [typ for _, typ in params]
            f = f"_root_.{name}"
            cands = []
            if len(params) == 2 and types == [ret, "Nat"] and ret in ("Int", "Nat") and name in recursive:
                b, e = params[0][0], params[1][0]
                cands.append((f"∀ ({b} : {ret}) ({e} : Nat), {f} {b} {e} = {b} ^ {e}",
                              f"by\n  intro {b} {e}; induction {e} with\n  | zero => simp [{f}]\n"
                              f"  | succ n ih => simp only [{f}, ih, pow_succ]; ring"))
            if not params and ret.replace(" ", "") == "ListNat→Nat":
                for base in (10, 2):
                    cands.append((f"∀ (l : List Nat), {f} l = Nat.ofDigits {base} l",
                                  f"by\n  intro l; induction l with\n  | nil => simp [{f}, Nat.ofDigits]\n"
                                  f"  | cons d ds ih => simp [{f}, Nat.ofDigits, ih]"))
            if len(params) == 2 and types[1] == f"List {types[0]}" and ret == types[1] and "let rec aux" in body:
                x, l = params[0][0], params[1][0]
                cands.append((f"∀ ({x} : {types[0]}) ({l} : {types[1]}), {f} {x} {l} = {l}.filter (fun y => decide (y = {x}))",
                              f"by\n  intro {x} {l}; unfold {f}; induction {l} with\n  | nil => simp [{f}.aux]\n"
                              f"  | cons y ys ih => simp only [{f}.aux, List.filter_cons]; split <;> simp_all"))
            # ``f (v : T) : List T → Nat`` counting ``v`` (Verina advanced_56: ``countVal``)
            if len(params) == 1 and ret.replace(" ", "") == f"List{types[0]}→Nat".replace(" ", "") and name in recursive:
                v = params[0][0]
                cands.append((f"∀ ({v} : {types[0]}) (l : List {types[0]}), {f} {v} l = l.count {v}",
                              f"by\n  intro {v} l; induction l with\n  | nil => simp [{f}]\n"
                              f"  | cons y ys ih => simp only [{f}, ih, List.count_cons]; split <;> simp_all"))
            # ``f (xs ys : List T) : Bool`` deciding "xs is a subsequence of ys" (Verina advanced_56: ``isSubsequence``)
            if len(params) == 2 and types[0] == types[1] and types[0].startswith("List") and ret == "Bool" \
                    and name in recursive:
                xs, ys = params[0][0], params[1][0]
                cands.append((f"∀ ({xs} {ys} : {types[0]}), {f} {xs} {ys} = true ↔ {xs}.Sublist {ys}",
                              f"by\n  intro {xs} {ys}; induction {xs}, {ys} using {f}.induct <;> simp_all [{f}]\n"
                              "  all_goals grind [List.cons_sublist_cons, List.sublist_cons_iff]"))
            for k, (statement, proof) in enumerate(cands):
                if self._admit(HelperLemma(f"auto_libeq_{name}_{k}", statement, proof)) is None:
                    found = True
                    break
        return found

    def _recursive_defs(self) -> List[str]:
        """The task's own functions defined by recursion on their argument (they have an ``.induct`` principle)."""
        out = []
        for name in self._task_defs():
            body = re.split(rf"(?m)^\s*(?:@\[[^\]]*\]\s*)?def\s+{re.escape(name)}\b", self.task.prelude, maxsplit=1)
            if len(body) > 1 and re.search(rf"\b{re.escape(name)}\b", re.split(r"(?m)^\S", body[1], maxsplit=1)[0]):
                out.append(name)
        return out

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
        # the task's hand-written recursive helpers recognised as library functions (``pow`` is ``^``, a digit fold is
        # ``Nat.ofDigits``, a ``let rec`` filter is ``List.filter``): proved once, they join the cascade's rewrite rules
        if not self._libeq_tried:
            self._libeq_tried = True
            with self.phase("library_equations"):
                added = self._library_equations()
            if added:
                verdict = self._check_once(obligation, name)
                if verdict.status != "UNPROVED" or verdict.counterexample:
                    return verdict
        # tactics the common cascade does not contain (they depend on this obligation): each proof found becomes a helper
        specials = [t for t in (self._witness_tactic(obligation), self._cases_tactic(obligation)) if t]
        specials += self._shape_tactics(obligation)
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
            reply = self._run(source, timeout=PLAUSIBLE_TIMEOUT)
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
