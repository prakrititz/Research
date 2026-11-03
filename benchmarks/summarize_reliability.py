"""One table from many reliability result files: arm, trials, successes, Wilson interval, calls, time.

    python benchmarks/summarize_reliability.py "benchmarks/results/reliability/v5_*.jsonl"
    python benchmarks/summarize_reliability.py "benchmarks/results/reliability/*/*.jsonl" --markdown
"""
import argparse
import collections
import glob
import json
import math
import os
import statistics
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from FormalLLM.llm.transport import NETWORK, effective_outcome      # noqa: E402


def wilson(successes: int, n: int, z: float = 1.96):
    if n == 0:
        return (0.0, 1.0)
    p = successes / n
    centre = (p + z * z / (2 * n)) / (1 + z * z / n)
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return (max(0.0, centre - half), min(1.0, centre + half))


def load(pattern: str):
    arms = collections.OrderedDict()
    for path in sorted(glob.glob(pattern)):
        arm = os.path.basename(path).rsplit("_", 1)[0]
        for line in open(path, encoding="utf8"):
            if line.strip():
                arms.setdefault(arm, []).append(json.loads(line))
    return arms


def summarize(rows):
    """Success counts. A trial that never reached the model (every call failed to connect) is shown
    as NETWORK and left out of the rate: it says nothing about the method."""
    outcomes = collections.Counter(effective_outcome(r) for r in rows)
    all_rows, rows = rows, [r for r in rows if effective_outcome(r) != NETWORK]
    n = len(rows)
    ok = [r for r in rows if r["outcome"] == "SUCCESS"]
    low, high = wilson(len(ok), n)
    certified = [r for r in ok if r.get("certificate") and "coq" in r["certificate"]]
    fully = sum(1 for r in certified
                if r["certificate"]["coq"]["certified"] == r["certificate"]["obligations"])
    return {
        "n": n, "n_all": len(all_rows), "ok": len(ok), "low": low, "high": high, "outcomes": dict(outcomes),
        "calls_median": statistics.median(r["llm_calls"] for r in ok) if ok else None,
        "calls_max": max((r["llm_calls"] for r in ok), default=None),
        "calls_mean_all": statistics.mean(r["llm_calls"] for r in rows) if rows else None,
        "wall_median": statistics.median(r["wall_s"] for r in ok) if ok else None,
        "certified_fully": fully, "certified_of": len(certified),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pattern")
    ap.add_argument("--markdown", action="store_true")
    args = ap.parse_args()
    arms = load(args.pattern)
    header = ["arm", "trials", "success", "95% interval", "calls median (max)", "mean calls (all)", "wall median s",
              "other outcomes", "Coq-certified"]
    rows = []
    for arm, data in arms.items():
        s = summarize(data)
        others = {k: v for k, v in s["outcomes"].items() if k != "SUCCESS"}
        rows.append([arm, s["n_all"], f"{s['ok']}/{s['n']} = {100 * s['ok'] / max(s['n'], 1):.0f}%",
                     f"{100 * s['low']:.0f}% - {100 * s['high']:.0f}%",
                     f"{s['calls_median']} ({s['calls_max']})", f"{s['calls_mean_all'] or 0:.1f}",
                     f"{s['wall_median']:.0f}" if s["wall_median"] is not None else "-",
                     ", ".join(f"{k} {v}" for k, v in others.items()) or "-",
                     f"{s['certified_fully']}/{s['certified_of']}" if s["certified_of"] else "-"])
    if args.markdown:
        print("| " + " | ".join(header) + " |")
        print("|" + "---|" * len(header))
        for row in rows:
            print("| " + " | ".join(str(x) for x in row) + " |")
    else:
        widths = [max(len(str(x)) for x in col) for col in zip(header, *rows)]
        for row in [header] + rows:
            print("  ".join(str(x).ljust(w) for x, w in zip(row, widths)))


if __name__ == "__main__":
    main()
