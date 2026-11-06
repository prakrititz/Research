"""Lean check that the L_spec tooling changes no meaning: every proof obligation and helper-lemma statement of every
hand-written derivation, generated once from the original tree and once from the transformed tree, elaborates to the
same Lean term.

    python benchmarks/lspec_equiv.py --dataset humaneval [--transform lspec] [--only ID ...]

The engine builds obligations in Python (``Law.expand``); only proving them needs Lean. So the derivation is replayed
twice with the prover stubbed out (every obligation "proved", every helper accepted), which collects the obligations of
both trees. Pairs whose text is identical need nothing; for every other pair Lean elaborates both sides in the task's
environment and requires the two terms to be *structurally* equal (``Expr`` equality up to binder names, not just
definitional equality, so ``2 + 2`` and ``4`` count as different). A derivation passes when its two obligation lists
have the same shape and every pair is equal.

This is stricter than re-certifying (``lspec_roundtrip.py``): re-certifying shows the transformed derivation is still
*correct*; this shows it is the *same* derivation. And it costs seconds per task instead of the full proof search.
Results: ``benchmarks/results/lspec/equiv_<transform>_<dataset>.jsonl`` (resumable)."""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from lspec_roundtrip import transform_tree  # noqa: E402

#: elaborate two terms and require structural equality (``==`` on ``Expr`` is alpha-equivalence)
SAME = r"""
open Lean Elab Command Term Meta in
elab "#lspec_same " a:term:max b:term:max : command => liftTermElabM do
  let ea ← elabTerm a none
  synthesizeSyntheticMVarsNoPostponing
  let ea ← instantiateMVars ea
  let eb ← elabTerm b none
  synthesizeSyntheticMVarsNoPostponing
  let eb ← instantiateMVars eb
  unless ea == eb do
    throwError m!"lspec_differ:\n{ea}\n----\n{eb}"

open Lean Elab Command Term Meta in
/-- `#lspec_same_beta a b`: structurally equal once every `(fun x => t) v` is reduced (for a goal shown with the
lambda already applied; nothing else is unfolded). -/
elab "#lspec_same_beta " a:term:max b:term:max : command => liftTermElabM do
  let ea ← elabTerm a none
  synthesizeSyntheticMVarsNoPostponing
  let ea ← Core.betaReduce (← instantiateMVars ea)
  let eb ← elabTerm b none
  synthesizeSyntheticMVarsNoPostponing
  let eb ← Core.betaReduce (← instantiateMVars eb)
  unless ea == eb do
    throwError m!"lspec_differ:\n{ea}\n----\n{eb}"

open Lean Elab Command Meta in
/-- `#lspec_same_consts a b`: the constants `a` and `b`, and every constant declared under them (the functions a
`let rec` lifts out, matchers, equation helpers), are equal once the prefix `b` is read as `a`. For terms that declare
things (`let rec`), which cannot be elaborated twice side by side. -/
elab "#lspec_same_consts " a:ident b:ident : command => do
  let env ← getEnv
  let na := a.getId
  let nb := b.getId
  let ren (e : Expr) : Expr := e.replace fun x => match x with
    | .const n us => if nb.isPrefixOf n then some (.const (n.replacePrefix nb na) us) else none
    | _ => none
  let mut seen := 0
  for (n, ci) in env.constants.map₂.toList do
    unless nb.isPrefixOf n do continue
    let n' := n.replacePrefix nb na
    let some ci' := env.find? n' | throwError m!"lspec_differ: {n} has no counterpart {n'}"
    unless ren ci.type == ci'.type do
      throwError m!"lspec_differ: the types of {n'} and {n}:\n{ci'.type}\n----\n{ci.type}"
    match ci.value?, ci'.value? with
    | some v, some v' =>
      unless ren v == v' do
        throwError m!"lspec_differ: the values of {n'} and {n}:\n{v'}\n----\n{ren v}"
    | _, _ => pure ()
    seen := seen + 1
  if seen == 0 then throwError m!"lspec_differ: nothing declared under {nb}"
"""


def closed(binders: str, statement: str) -> str:
    """The obligation as one closed proposition."""
    return f"(∀ {binders}, {statement})" if binders.strip() else f"({statement})"


def collect(task_id: str, tree: dict):
    """Replay ``tree`` with the prover stubbed out: the obligations (kind, closed statement, body), the helper-lemma
    statements, and the task (for its Lean environment). An obligation checked by elaboration (``body``: e.g. a
    well-formedness check, whose body is the proposition itself) keeps its body, ascribed its statement (``inferInstance`` needs
    its expected type), as a function of its binders."""
    from FormalLLM.lean import engine
    from FormalLLM.lean.dataset import resolve
    task = resolve(task_id).load(task_id)
    derivation = engine.Derivation(task, lean=None, counterexamples=False)
    seen = []

    def check(obligation, name):
        seen.append(("obligation", obligation.kind, closed(obligation.binders, obligation.statement),
                     obligation.body and (f"(fun {obligation.binders} => ({obligation.body} : {obligation.statement}))"
                                          if obligation.binders.strip() else f"({obligation.body} : {obligation.statement})")))
        return engine.Verdict(obligation, "PROVED")

    def admit(lemma):
        seen.append(("lemma", lemma.name, f"({lemma.statement})", None))
        derivation.helpers.append(lemma)
        return None
    derivation._check, derivation._admit = check, admit
    steps = derivation.apply_tree(tree)
    if not all(s.ok for s in steps) or not derivation.complete:
        raise ValueError("the stubbed replay did not complete: " + "; ".join(s.message for s in steps if not s.ok)[:200])
    return task, derivation, seen


_BASE = {}


def base_env(lean, lemmas: str) -> int:
    """The engine's lemma library and ``#lspec_same``, loaded once (again after a restart of the session); each task's
    own definitions go on top of it."""
    key = (lemmas, lean.restarts)
    if key not in _BASE:
        reply, env = lean.load(lemmas + "\n" + SAME, timeout=1200)
        if env is None:
            raise RuntimeError("the lemma library does not load: " + (reply.errors or ["timeout"])[0][:300])
        _BASE[key] = env
    return _BASE[key]


#: the check must tell these apart (regrouping, a definitional unfolding, a coercion moved) and accept the last ones
CONTROLS = [("(∀ a b c : Nat, a - b - c = 0)", "(∀ a b c : Nat, a - (b - c) = 0)", False),
            ("(2 + 2 : Nat)", "(4 : Nat)", False),
            ("(∀ (k : Nat) (e : ℚ), (k + 1 : ℚ) * e ≤ 1)", "(∀ (k : Nat) (e : ℚ), ((k + 1 : Nat) : ℚ) * e ≤ 1)", False),
            ("(∀ (l : List Int), l.length > 0 → l[0]! ≥ 0)", "(∀ (l : List Int), (l.length > 0) → (l[0]! ≥ 0))", True),
            ("(∀ (N e : ℚ), N ≤ e)", "(∀ (N : Rat) (e : Rat), (N) ≤ (e))", True)]


def control(lean) -> None:
    """A negative and positive control, run before any task: a check that passes everything proves nothing."""
    env = base_env(lean, __import__("FormalLLM.lean.lemmas", fromlist=["LEMMAS"]).LEMMAS
                   + "\n" + __import__("FormalLLM.lean.engine", fromlist=["AUTO_CLOSE"]).AUTO_CLOSE)
    for a, b, same in CONTROLS:
        reply = lean.run(f"#lspec_same {a} {b}\n", timeout=120, env=env)
        if (not reply.errors and not reply.timed_out) != same:
            raise SystemExit(f"control failed: {a} vs {b} should be {'equal' if same else 'different'}: {reply.errors[:1]}")
    print(f"controls passed ({len(CONTROLS)})", flush=True)


def compare(task_id: str, tree: dict, how: str, lean) -> dict:
    row = {"id": task_id, "same": False, "obligations": 0, "differing": 0, "errors": []}
    started = time.time()
    try:
        new_tree = transform_tree(tree, how)
    except Exception as error:
        row["errors"].append(f"transform: {str(error)[:300]}")
        return row
    task, derivation, before = collect(task_id, tree)
    _, _, after = collect(task_id, new_tree)
    row["obligations"] = len(before)
    if [(k, n) for k, n, *_ in before] != [(k, n) for k, n, *_ in after]:
        row["errors"].append("the two trees give differently shaped obligation lists")
        return row
    pairs = []
    for (_, _, s1, b1), (_, _, s2, b2) in zip(before, after):
        if s1 != s2:
            pairs.append((s1, s2))
        if (b1 or "") != (b2 or ""):
            pairs.append((b1 or "True", b2 or "True"))
    row["differing"] = len(pairs)
    if pairs:
        reply, env = lean._run(task.prelude + "\n" + derivation._helper_text(), 600, base_env(lean, derivation.lemmas))
        if env is None:
            row["errors"].append("environment: " + (reply.errors or ["timeout"])[0][:300])
            return row
        for s1, s2 in pairs:
            reply = lean.run(f"#lspec_same {s1} {s2}\n", timeout=300, env=env)
            if reply.timed_out or reply.errors:
                row["errors"].append({"before": s1[:400], "after": s2[:400],
                                      "lean": (reply.errors or ["timeout"])[0][:600]})
    row["same"] = not row["errors"]
    row["seconds"] = round(time.time() - started, 1)
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--transform", default="lspec", choices=["lean", "lspec"])
    ap.add_argument("--only", nargs="*")
    args = ap.parse_args()
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession

    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"equiv_{args.transform}_{args.dataset}.jsonl")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    done = set()
    if os.path.exists(out):
        done = {json.loads(line)["id"] for line in open(out, encoding="utf8") if line.strip()}
    todo = [t for t in trees if t not in done and (not args.only or t in args.only)]
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        control(lean)
        for task_id in todo:
            try:
                row = compare(task_id, trees[task_id], args.transform, lean)
            except Exception as error:
                row = {"id": task_id, "same": False, "errors": [f"{type(error).__name__}: {str(error)[:300]}"]}
            print(f"{task_id:32s} {'SAME' if row['same'] else 'DIFF'}  obligations {row.get('obligations', '?')}  "
                  f"rewritten {row.get('differing', '?')}  {row.get('seconds', '')}s  "
                  f"{'' if row['same'] else str(row['errors'][0])[:160]!r}", flush=True)
            with open(out, "a", encoding="utf8") as handle:
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    print(f"{sum(r['same'] for r in rows)} of {len(rows)} {args.dataset} derivations unchanged in meaning after "
          f"--transform {args.transform} ({len(trees)} derivations)")


if __name__ == "__main__":
    main()
