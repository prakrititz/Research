"""Phase 3 (counterexamples without Z3): how often does a small-input search refute what Z3 refuted?

Z3's counterexample is what the refiner feeds back to the model after a rejected step. If Lean replaces Z3, Lean says only
"unknown". The existing evaluator (``lspec/evaluator.py``) can instead *search small inputs* for a state that satisfies the
assumptions and falsifies the goal. This script measures how good that is on real data: it replays stored runs rich in
rejections, records every obligation Z3 FAILED (so a counterexample exists), and runs the small-input search on each.

    python benchmarks/cex_by_testing.py [--per-file N]       # writes benchmarks/results/lean_audit/cex_by_testing.json
"""
import argparse
import collections
import contextlib
import glob
import io
import itertools
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "benchmarks", "results", "lean_audit")
INTS = [-3, -2, -1, 0, 1, 2, 3, 4, 5, 8, 10]
REALS = [-2, -1, 0, 1, 2, 3, 0.5, -0.5, 4, 10]
CAP = 40000


def free_names(obligation):
    from FormalLLM.lspec.substitution import get_free_vars
    names = set()
    for expr in list(obligation.assumptions) + [obligation.goal]:
        names |= get_free_vars(expr)
    return sorted(names)


def definitions(obligation, names):
    """Variables an assumption pins down by an equation ``v = expr(others)`` (greedy, no cycles): ``[(v, expr)]``."""
    from FormalLLM.lspec.ast import BinaryOp, Const, Variable
    from FormalLLM.lspec.substitution import get_free_vars
    from FormalLLM.refinement.frame import split_conjunction
    out, defined = [], set()
    for assumption in obligation.assumptions:
        for conjunct in split_conjunction(assumption):
            if isinstance(conjunct, BinaryOp) and conjunct.op == "=":
                for mine, rest in ((conjunct.left, conjunct.right), (conjunct.right, conjunct.left)):
                    if isinstance(mine, (Variable, Const)) and mine.name in names and mine.name not in defined:
                        needs = get_free_vars(rest)
                        if mine.name not in needs and not (needs & {v for v, _ in out if v == mine.name}):
                            if all(n not in defined or True for n in needs) and not any(
                                    mine.name in get_free_vars(e) and v in needs for v, e in out):
                                out.append((mine.name, rest))
                                defined.add(mine.name)
                                break
    return out


def search(obligation):
    """A counterexample by enumeration of the free *inputs*, with definitional equalities computed: ``(values, tried)``,
    ``(None, tried)``, or ``(None, -1)`` if the obligation mentions arrays."""
    from FormalLLM.lspec import evaluator
    from FormalLLM.lspec.ast import ArrayType, BoolType, FloatType
    types = {p.name: p.type_ for p in getattr(obligation, "params", [])}
    names = free_names(obligation)
    defs = definitions(obligation, set(names))
    derived = [v for v, _ in defs]
    base = [n for n in names if n not in derived]
    domains = []
    for name in base:
        t = types.get(name)
        if isinstance(t, ArrayType):
            return None, -1
        domains.append([True, False] if isinstance(t, BoolType) else (REALS if isinstance(t, FloatType) else INTS))
    tried = satisfied = 0
    for combo in itertools.product(*domains):
        tried += 1
        if tried > CAP:
            break
        env = dict(zip(base, combo))
        try:
            for _ in range(len(defs) + 1):                     # let definitions feed each other, in any order
                for name, expr in defs:
                    try:
                        env[name] = evaluator.evaluate(expr, env)
                    except KeyError:
                        pass
            if len(env) < len(names):
                continue
            if all(evaluator.evaluate(a, env) for a in obligation.assumptions):
                satisfied += 1
                if not evaluator.evaluate(obligation.goal, env):
                    return env, tried
        except Exception:
            continue
    search.last_satisfied = satisfied
    return None, tried


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--per-file", type=int, default=12)
    args = ap.parse_args()
    from benchmarks.cases import CASES
    from benchmarks.lean_audit_collect import rebuild
    from FormalLLM.verification import z3_backend as zb
    from FormalLLM.verification.backends import Z3Backend
    cases = {c["id"]: c for c in CASES}
    failed = []                                                    # obligations Z3 refuted during the replays
    original = Z3Backend.verify

    def recording(self, obligation, timeout_ms=None):
        status, message = original(self, obligation, timeout_ms)
        if status == "FAILED":
            failed.append(obligation)
        return status, message
    Z3Backend.verify = recording
    files = (glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/cases_D1-intdiv_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v6_relaxed_noassist_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v6_strict_assist_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/cases_A4-impossible_*.jsonl")))
    replayed = 0
    for path in files:
        count = 0
        for line in open(path, encoding="utf8"):
            if not line.strip() or count >= args.per_file:
                continue
            row = json.loads(line)
            if not row.get("raw_responses"):
                continue
            count += 1
            replayed += 1
            try:
                rebuild(row, cases)
            except Exception:
                pass
    Z3Backend.verify = original
    seen, rows = set(), []
    for ob in failed:
        key = repr((ob.assumptions, ob.goal))
        if key in seen:
            continue
        seen.add(key)
        started = time.time()
        search.last_satisfied = 0
        found, tried = search(ob)
        rows.append({"assumptions_ever_satisfied": search.last_satisfied > 0 or found is not None, "description": getattr(ob, "description", "")[:70], "searchable": tried != -1,
                     "found": found is not None, "tried": tried, "seconds": round(time.time() - started, 3)})
    searchable = [r for r in rows if r["searchable"]]
    summary = {"runs_replayed": replayed, "z3_refutations_total": len(failed), "distinct": len(rows),
               "searchable_scalar": len(searchable), "found_by_small_inputs": sum(r["found"] for r in searchable),
               "not_searchable_arrays": len(rows) - len(searchable),
               "unfound_but_assumptions_never_satisfied": sum(1 for r in searchable if not r["found"] and not r["assumptions_ever_satisfied"]),
               "unfound_assumptions_satisfied_goal_always_true": sum(1 for r in searchable if not r["found"] and r["assumptions_ever_satisfied"]),
               "median_seconds": sorted(r["seconds"] for r in searchable)[len(searchable) // 2] if searchable else None,
               "by_description": dict(collections.Counter(r["description"] for r in rows if r["searchable"] and not r["found"]))}
    os.makedirs(OUT, exist_ok=True)
    json.dump({"summary": summary, "rows": rows}, open(os.path.join(OUT, "cex_by_testing.json"), "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
