"""The HumanEval pilot, one row per problem: the model alone, a hand derivation, and refinement runs.

    python benchmarks/pilot_compare.py                                   # the default files below
    python benchmarks/pilot_compare.py --new benchmarks/results/datasets/he_refine_v8.jsonl \
        --old benchmarks/results/datasets/he_refine_z3.jsonl benchmarks/results/datasets/he_refine_z3_lean.jsonl

Columns: whether the model *alone* (no refinement) passes the original and the EvalPlus tests; whether a
derivation written by hand is accepted by the engine (``he_oracle``); how many refinement runs derived a
program with the old code and with the new code; how many derived programs pass every test; the median
number of model calls of a successful run; and how many successful runs Coq certified completely.
Runs lost to the network (``NETWORK``) are not counted.
"""
import argparse
import collections
import json
import os
import statistics
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
DATA = os.path.join(ROOT, "benchmarks", "results", "datasets")


def load(paths):
    """Rows of the given files, without runs that never reached the model or were cut off by the endpoint."""
    from FormalLLM.llm.transport import NETWORK, effective_outcome
    out = []
    for path in paths:
        if not os.path.exists(path):
            continue
        for line in open(path, encoding="utf8"):
            if line.strip():
                row = json.loads(line)
                if effective_outcome(row) != NETWORK:
                    out.append(row)
    return out


def by_task(rows):
    grouped = collections.defaultdict(list)
    for row in rows:
        grouped[row["task_id"]].append(row)
    return grouped


def derived(runs):
    return "–" if not runs else f"{sum(r['outcome'] == 'SUCCESS' for r in runs)}/{len(runs)}"


def passing(runs):
    ok = [r for r in runs if r["outcome"] == "SUCCESS"]
    if not ok:
        return "–"
    return (f"{sum(r.get('base') == 'pass' for r in ok)}/{len(ok)} · "
            f"{sum(r.get('plus') == 'pass' for r in ok)}/{len(ok)}")


def median_calls(runs):
    ok = [r["llm_calls"] for r in runs if r["outcome"] == "SUCCESS"]
    return "–" if not ok else f"{statistics.median(ok):g}"


def coq_certified(runs):
    ok = [r for r in runs if r["outcome"] == "SUCCESS" and isinstance(r.get("certificate"), dict)
          and "coq" in r["certificate"]]
    if not ok:
        return "–"
    full = sum(r["certificate"]["coq"].get("certified") == r["certificate"].get("obligations") for r in ok)
    return f"{full}/{len(ok)}"


def word(flag):
    return {True: "pass", False: "FAIL"}.get(flag, "?")


def table(new_rows, old_rows, baseline_rows):
    from benchmarks.datasets.he_oracle import ORACLE
    from benchmarks.datasets.he_specs import SPECS
    alone = {r["task_id"]: (r.get("base_ok"), r.get("plus_ok")) for r in baseline_rows}
    new, old = by_task(new_rows), by_task(old_rows)
    order = sorted(SPECS, key=lambda t: ("ABC".index(SPECS[t]["tier"]), int(t.split("/")[1])))
    lines = ["| Problem | Tier | Model alone (base · plus) | Hand derivation | Old code: derived | New code: derived "
             "| Derived programs pass (base · plus) | Calls, median | Coq-certified |",
             "|---|---|---|---|---|---|---|---|---|"]
    for t in order:
        b = alone.get(t, (None, None))
        lines.append(f"| {t.split('/')[1]} `{SPECS[t]['name']}` | {SPECS[t]['tier']} | {word(b[0])} · {word(b[1])} | "
                     f"{'yes' if t in ORACLE else 'no'} | {derived(old.get(t, []))} | {derived(new.get(t, []))} | "
                     f"{passing(new.get(t, []))} | {median_calls(new.get(t, []))} | {coq_certified(new.get(t, []))} |")
    return "\n".join(lines), new, old


def totals(grouped, tiers):
    runs = [r for t, rs in grouped.items() for r in rs]
    ok = [r for r in runs if r["outcome"] == "SUCCESS"]
    plus = [r for r in ok if r.get("plus") == "pass" and r.get("base") == "pass"]
    problems = sum(any(r["outcome"] == "SUCCESS" for r in rs) for rs in grouped.values())
    per_tier = collections.defaultdict(lambda: [0, 0])
    for t, rs in grouped.items():
        per_tier[tiers[t]][0] += sum(r["outcome"] == "SUCCESS" for r in rs)
        per_tier[tiers[t]][1] += len(rs)
    outcomes = collections.Counter(r["outcome"] for r in runs)
    return (f"{len(ok)} of {len(runs)} runs derived a program ({problems} of {len(grouped)} problems at least once); "
            f"{len(plus)} of the {len(ok)} derived programs pass every original and EvalPlus test; by tier: "
            + ", ".join(f"{k} {v[0]}/{v[1]}" for k, v in sorted(per_tier.items()))
            + "; outcomes: " + ", ".join(f"{k} {v}" for k, v in sorted(outcomes.items())))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    # all v8-code pilot runs: the two passes, the held-out run, and the parallel launcher's run (labelled v7)
    ap.add_argument("--new", nargs="*", default=[os.path.join(DATA, name) for name in
                                                 ("he_refine_v8.jsonl", "he_refine_v8_heldout.jsonl",
                                                  "he_refine_v7.jsonl")])
    ap.add_argument("--old", nargs="*", default=[os.path.join(DATA, "he_refine_z3.jsonl"),
                                                 os.path.join(DATA, "he_refine_z3_lean.jsonl")])
    ap.add_argument("--baseline", default=os.path.join(DATA, "direct_baseline_gpt-oss-120b-low_rescored.jsonl"))
    args = ap.parse_args(argv)
    from benchmarks.datasets.he_specs import SPECS
    text, new, old = table(load(args.new), load(args.old), load([args.baseline]))
    print(text)
    tiers = {t: SPECS[t]["tier"] for t in SPECS}
    print()
    print("old code: " + (totals(old, tiers) if old else "no runs"))
    print("new code: " + (totals(new, tiers) if new else "no runs"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
