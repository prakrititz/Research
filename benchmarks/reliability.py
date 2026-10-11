"""Reliability study: run one case N times and report how often refinement succeeds.

"It worked once" is not a result. The paper's square-root example succeeded in
1 of 2 committed trials, and a single trial of the current prompts failed; the
goal is a system that solves it *every* time, so the question to answer is a
rate with an interval, over enough independent trials to tell 19/20 from 10/20.

Each trial gets its own provider (and, if ``--seed-base`` is given, its own
sampling seed so a trial can be replayed). Every trial's console transcript is
kept on disk so a failure can be read, not guessed at; the JSONL result is
appended after every trial so an interrupted study keeps what it has.

    python benchmarks/reliability.py --config gpt-oss-120b-low --trials 20
"""
import argparse
import contextlib
import io
import json
import math
import os
import statistics
import sys
import tempfile
import time
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from cases import CASES_BY_ID           # noqa: E402
from harness import run_trial           # noqa: E402
import run_bench                        # noqa: E402


def wilson(successes: int, n: int, z: float = 1.96):
    """95 % Wilson score interval for a proportion (well behaved at 0 and n)."""
    if n == 0:
        return 0.0, 0.0
    p = successes / n
    denom = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / denom
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / denom
    return max(0.0, centre - half), min(1.0, centre + half)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--config", default="gpt-oss-120b-low", help="a name from run_bench.CONFIGS")
    ap.add_argument("--case", default="C5-sqrt-paper")
    ap.add_argument("--trials", type=int, default=10)
    ap.add_argument("--turns", type=int, choices=(1, 2), default=2,
                    help="2 = law choice then parameters (the paper's Algorithm 1); 1 = one call per step")
    ap.add_argument("--max-retries", type=int, default=4)
    ap.add_argument("--budget", type=int, default=40, help="LLM calls allowed per trial")
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--strict", choices=("1", "0"), default=None,
                    help="FORMALLLM_STRICT_VARIANT for this study (1 = require 0 <= V)")
    ap.add_argument("--assist", action="store_true",
                    help="let the prover close one-line leaves without an LLM call (not in the paper)")
    ap.add_argument("--certify", nargs="*", default=None, choices=("coq", "lean"),
                    help="after a successful trial, have these proof assistants re-check its derivation")
    ap.add_argument("--seed-base", type=int, default=None)
    ap.add_argument("--label", default=None, help="name for the output files")
    ap.add_argument("--out", default=None)
    ap.add_argument("--transcripts", default=None, help="directory for per-trial transcripts")
    args = ap.parse_args()

    if args.strict is not None:
        os.environ["FORMALLLM_STRICT_VARIANT"] = args.strict
    if args.config not in run_bench.CONFIGS:
        raise SystemExit(f"unknown config {args.config!r}; known: {sorted(run_bench.CONFIGS)}")
    if args.case not in CASES_BY_ID:
        raise SystemExit(f"unknown case {args.case!r}; known: {sorted(CASES_BY_ID)}")
    case, cfg = CASES_BY_ID[args.case], run_bench.CONFIGS[args.config]

    label = args.label or f"{args.config}_{args.case}_t{args.turns}"
    stamp = time.strftime("%Y%m%d-%H%M%S")
    out = args.out or os.path.join(ROOT, "benchmarks", "results", "reliability", f"{label}_{stamp}.jsonl")
    tdir = args.transcripts or os.path.join(tempfile.gettempdir(), "runs", "transcripts", f"{label}_{stamp}")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    os.makedirs(tdir, exist_ok=True)

    print(f"study: {label}  trials={args.trials}  turns={args.turns}  budget={args.budget}  "
          f"max_retries={args.max_retries}  strict={os.environ.get('FORMALLLM_STRICT_VARIANT', '1')}  "
          f"assist={args.assist}", flush=True)
    print(f"results -> {out}\ntranscripts -> {tdir}", flush=True)

    records = []
    for i in range(args.trials):
        seed = None if args.seed_base is None else args.seed_base + i
        provider = run_bench.make_provider(cfg, args.temperature, args.timeout, seed=seed)
        transcript = io.StringIO()
        t0 = time.time()
        with contextlib.redirect_stdout(transcript):
            rec = run_trial(case, provider, i, args.config, max_retries=args.max_retries,
                            budget=args.budget, law_set=None, max_depth=args.max_depth,
                            use_multi_turn=(args.turns == 2), assist=args.assist,
                            certify=args.certify)
        rec.update(turns=args.turns, seed=seed, temperature=args.temperature,
                   strict_variant=os.environ.get("FORMALLLM_STRICT_VARIANT", "1"),
                   label=label, max_retries=args.max_retries, budget=args.budget)
        with open(os.path.join(tdir, f"trial_{i:02d}.txt"), "w", encoding="utf8") as fh:
            fh.write(transcript.getvalue())
        with open(out, "a", encoding="utf8") as fh:
            fh.write(json.dumps(rec) + "\n")
        records.append(rec)
        ok = sum(r["outcome"] == "SUCCESS" for r in records)
        cert = ""
        if rec.get("certificate") and "obligations" in rec["certificate"]:
            c = rec["certificate"]
            cert = "  certified: " + ", ".join(f"{n} {c[n]['certified']}/{c['obligations']}"
                                               for n in c if n != "obligations")
        print(f"[{i + 1:2d}/{args.trials}] {rec['outcome']:<9} calls={rec['llm_calls']:<3} "
              f"wall={rec['wall_s']:>7.1f}s   running: {ok}/{len(records)}{cert}", flush=True)

    lost = sum(r["outcome"] == "NETWORK" for r in records)        # never reached the model: not a method failure
    n = len(records) - lost
    k = sum(r["outcome"] == "SUCCESS" for r in records)
    if n == 0:
        print("\n==== summary ====\nno trial reached the model; nothing to report.")
        return
    lo, hi = wilson(k, n)
    wins = [r for r in records if r["outcome"] == "SUCCESS"]
    print("\n==== summary ====")
    print(f"success: {k}/{n} = {k / n:.0%}   (95% Wilson interval {lo:.0%} - {hi:.0%})")
    print("outcomes:", dict(Counter(r["outcome"] for r in records)))
    if lost:
        print(f"{lost} trial(s) lost to network errors are not counted in the rate above.")
    if wins:
        calls = [r["llm_calls"] for r in wins]
        walls = [r["wall_s"] for r in wins]
        print(f"successful trials: calls median {statistics.median(calls)} (min {min(calls)}, max {max(calls)}); "
              f"wall median {statistics.median(walls):.0f}s")
    print(f"all trials: mean calls {statistics.mean(r['llm_calls'] for r in records):.1f}, "
          f"mean wall {statistics.mean(r['wall_s'] for r in records):.0f}s")


if __name__ == "__main__":
    main()
