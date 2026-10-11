"""Phase A of the post-meeting plan: score the HumanEval pilot per PROBLEM, not per run.

The paper evaluates each question over several tries, averages, and counts it solved above a threshold. Our
earlier tables counted runs ("41 of 121"). Here, from the stored runs only (no model, no prover), a problem is
solved at threshold t if the fraction of its valid runs that are *solved* is at least t. A run is solved in
two senses: "derived" (the derivation completed) and "verified" (derived, every original and EvalPlus test
passes, and Coq certified every obligation). Runs lost to the network are left out.

    python benchmarks/pilot_per_problem.py            # prints Markdown, writes pilot_per_problem.md next to the data
"""
import collections
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
DATA = os.path.join(ROOT, "benchmarks", "results", "datasets")
FILES = ("he_refine_v8.jsonl", "he_refine_v8_heldout.jsonl", "he_refine_v7.jsonl")      # all v8 code
THRESHOLDS = (0.2, 0.4, 0.5, 0.6, 0.8, 1.0)


def coq_complete(row):
    cert = row.get("certificate")
    return isinstance(cert, dict) and "coq" in cert and cert["coq"].get("certified") == cert.get("obligations")


def load():
    from FormalLLM.llm.transport import NETWORK, effective_outcome
    runs = collections.defaultdict(list)
    for name in FILES:
        for line in open(os.path.join(DATA, name), encoding="utf8"):
            if line.strip():
                row = json.loads(line)
                if effective_outcome(row) != NETWORK:
                    runs[row["task_id"]].append(row)
    return runs


def main():
    from benchmarks.datasets.he_specs import SPECS
    runs = load()
    order = sorted(SPECS, key=lambda t: ("ABC".index(SPECS[t]["tier"]), int(t.split("/")[1])))
    lines = ["| Problem | Tier | Runs | Derived | Verified | " + " | ".join(f">= {int(t * 100)}%" for t in THRESHOLDS) + " |",
             "|---|---|---|---|---|" + "---|" * len(THRESHOLDS)]
    solved_at = {t: 0 for t in THRESHOLDS}
    rates = []
    for task in order:
        rs = runs.get(task, [])
        n = len(rs)
        derived = sum(r["outcome"] == "SUCCESS" for r in rs)
        verified = sum(r["outcome"] == "SUCCESS" and r.get("base") == "pass" and r.get("plus") == "pass"
                       and coq_complete(r) for r in rs)
        rate = verified / n if n else 0.0
        rates.append(rate)
        marks = []
        for t in THRESHOLDS:
            ok = n > 0 and rate >= t - 1e-9 and verified > 0
            solved_at[t] += ok
            marks.append("yes" if ok else "-")
        lines.append(f"| {task.split('/')[1]} `{SPECS[task]['name']}` | {SPECS[task]['tier']} | {n} | {derived} | {verified} | "
                     + " | ".join(marks) + " |")
    total = len(order)
    lines.append("")
    lines.append("Problems solved (verified rate at least the threshold), out of %d: " % total
                 + ", ".join(f">= {int(t * 100)}%: **{solved_at[t]}**" for t in THRESHOLDS))
    lines.append("")
    lines.append(f"Mean per-problem verified rate (average of the {total} rates): **{sum(rates) / total:.3f}**; "
                 f"pooled over runs: {sum(len([1 for r in rs if r['outcome']=='SUCCESS' and r.get('base')=='pass' and r.get('plus')=='pass' and coq_complete(r)]) for rs in runs.values())} verified of "
                 f"{sum(len(rs) for rs in runs.values())} valid runs.")
    text = "\n".join(lines)
    print(text)
    with open(os.path.join(DATA, "pilot_per_problem.md"), "w", encoding="utf8") as handle:
        handle.write(text + "\n")


if __name__ == "__main__":
    main()
