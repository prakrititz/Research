"""Paper figures (static PNG, 300 dpi) from the stored result files:  python paper/make_figures.py [OUTDIR]

fig_reliability.png  - square-root success rate by code version, with Wilson 95 % intervals (one series).
fig_pilot.png        - HumanEval pilot: runs that derived a verified program that also passes every test, per problem,
                       old code vs v8.

Palette: the dataviz reference instance (slot 1 blue #2a78d6, slot 2 orange #eb6834), validated with
validate_palette.js (all checks pass, light mode). Text in ink colours, never the series colour.
"""
import collections
import glob
import json
import math
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt                                   # noqa: E402

# The repository root (this file lives in <root>/paper); FORMALLLM_DEV_COPY may point at a working copy with newer results.
MAIN = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.environ.get("FORMALLLM_DEV_COPY", MAIN)
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(MAIN, "paper")
sys.path.insert(0, DEV)
from FormalLLM.llm.transport import NETWORK, effective_outcome    # noqa: E402

BLUE, ORANGE = "#2a78d6", "#eb6834"
INK, INK2, GRID, SURFACE = "#0b0b0b", "#52514e", "#e4e3df", "#fcfcfb"

plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9, "axes.edgecolor": INK2, "axes.labelcolor": INK,
    "xtick.color": INK2, "ytick.color": INK2, "axes.spines.top": False, "axes.spines.right": False,
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
})


def wilson(k, n, z=1.96):
    if n == 0:
        return 0.0, 1.0
    p = k / n
    centre = (p + z * z / (2 * n)) / (1 + z * z / n)
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return max(0.0, centre - half), min(1.0, centre + half)


def count(pattern_list):
    k = n = 0
    for pattern in pattern_list:
        for path in glob.glob(pattern):
            for line in open(path, encoding="utf8"):
                if not line.strip():
                    continue
                row = json.loads(line)
                if effective_outcome(row) == NETWORK:          # never reached the model: not a trial
                    continue
                n += 1
                k += row.get("outcome") == "SUCCESS"
    return k, n


def reliability():
    rel_main = os.path.join(MAIN, "benchmarks", "results", "reliability")
    rel_dev = os.path.join(DEV, "benchmarks", "results", "reliability")
    # v1, v3, v4 are small early studies whose counts are recorded in Reading Material/14 (section 3);
    # v5, v6 and v8 are read from their result files.
    rows = [("v1", 9, 10), ("v3", 7, 10), ("v4", 29, 30)]
    for label, patterns in (("v5", [os.path.join(rel_main, "v5_before_relevance", "v5_relaxed_assist_*.jsonl")]),
                            ("v6", [os.path.join(rel_main, "v6_relaxed_assist_2026100*.jsonl")]),
                            # v8: two sets of 50 run side by side with the same code (the second labelled v7_ by
                            # a launcher that kept running; see Reading Material/19, section 10)
                            ("v8", [os.path.join(rel_dev, "v8_sqrt_assist_*.jsonl"),
                                    os.path.join(rel_dev, "v7_sqrt_assist_20261005*.jsonl")])):
        k, n = count(patterns)
        if n:
            rows.append((label, k, n))
    fig, ax = plt.subplots(figsize=(4.6, 2.6), dpi=300)
    xs = range(len(rows))
    for x, (label, k, n) in zip(xs, rows):
        lo, hi = wilson(k, n)
        p = k / n
        ax.plot([x, x], [lo * 100, hi * 100], color=BLUE, linewidth=2, solid_capstyle="round")
        ax.plot([x], [p * 100], marker="o", markersize=6, color=BLUE, markeredgecolor=SURFACE, markeredgewidth=1.5)
        ax.annotate(f"{k}/{n}", (x, hi * 100), textcoords="offset points", xytext=(0, 4), ha="center",
                    fontsize=7.5, color=INK2)
    ax.set_xticks(list(xs), [r[0] for r in rows])
    ax.set_ylim(30, 107)
    ax.set_yticks([40, 60, 80, 100])
    ax.set_ylabel("successful trials (%)")
    ax.set_xlabel("code version")
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    ax.set_title("Square root, paper's example: success by code version (95 % CI)", fontsize=8,
                 color=INK, loc="left")
    fig.tight_layout()
    path = os.path.join(OUT, "fig_reliability.png")
    fig.savefig(path)
    print("wrote", path, rows)


def pilot():
    from benchmarks.datasets.he_specs import SPECS
    data = os.path.join("benchmarks", "results", "datasets")

    def load(paths):
        grouped = collections.defaultdict(list)
        for path in paths:
            if os.path.exists(path):
                for line in open(path, encoding="utf8"):
                    if line.strip():
                        r = json.loads(line)
                        if effective_outcome(r) != NETWORK:     # derived AND the program passes every test
                            grouped[r["task_id"]].append(r["outcome"] == "SUCCESS" and r.get("base") == "pass"
                                                         and r.get("plus") == "pass")
        return grouped
    old = load([os.path.join(MAIN, data, "he_refine_z3.jsonl"), os.path.join(MAIN, data, "he_refine_z3_lean.jsonl")])
    v8_names = ("he_refine_v8.jsonl", "he_refine_v8_heldout.jsonl", "he_refine_v7.jsonl")   # all three: v8 code
    new_files = [os.path.join(DEV, data, name) for name in v8_names]
    if not any(os.path.exists(f) for f in new_files):                       # after the copy back to the main folder
        new_files = [os.path.join(MAIN, data, name) for name in v8_names]
    new = load(new_files)
    order = sorted(SPECS, key=lambda t: ("ABC".index(SPECS[t]["tier"]), int(t.split("/")[1])))
    order = [t for t in order if t in new or t in old]
    if not order:
        print("no pilot data yet")
        return
    fig, ax = plt.subplots(figsize=(6.8, 0.26 * len(order) + 1.1), dpi=300)
    for i, t in enumerate(order):
        y = len(order) - 1 - i
        for runs, colour, dy, label in ((old.get(t), ORANGE, 0.17, "old code (before tonight)"),
                                        (new.get(t), BLUE, -0.17, "v8")):
            if not runs:
                continue
            frac = sum(runs) / len(runs)
            ax.barh(y + dy, frac * 100, height=0.3, color=colour, label=label if i == 0 else None)
            ax.annotate(f"{sum(runs)}/{len(runs)}", (frac * 100, y + dy), textcoords="offset points",
                        xytext=(3, 0), va="center", fontsize=6.5, color=INK2)
    ax.set_yticks(range(len(order)), [f"{t.split('/')[1]} {SPECS[t]['name']} ({SPECS[t]['tier']})" for t in reversed(order)],
                  fontsize=7)
    ax.set_xlim(0, 112)
    ax.set_xticks([0, 25, 50, 75, 100])
    ax.set_xlabel("% of runs: verified program derived AND it passes every test")
    ax.grid(axis="x", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    handles, labels = ax.get_legend_handles_labels()
    seen = dict(zip(labels, handles))
    ax.legend(seen.values(), seen.keys(), frameon=False, fontsize=7, loc="lower right")
    ax.set_title("HumanEval pilot, 20 checked specifications: old code vs v8", fontsize=8.5, color=INK, loc="left")
    fig.tight_layout()
    path = os.path.join(OUT, "fig_pilot.png")
    fig.savefig(path)
    print("wrote", path)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    reliability()
    pilot()
