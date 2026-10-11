"""Where does the time go in a derivation? (the "efficiency" question)

    python benchmarks/time_breakdown.py "benchmarks/results/reliability/v6_relaxed_assist_*.jsonl"

For the successful trials of a reliability study: how long the model took, how long everything
else took (prover, search bookkeeping, the leaf assist), and how long the certificates took.
"""
import glob
import json
import statistics
import sys


def main(pattern: str) -> None:
    rows = []
    for path in sorted(glob.glob(pattern)):
        rows += [json.loads(line) for line in open(path, encoding="utf8") if line.strip()]
    ok = [r for r in rows if r["outcome"] == "SUCCESS"]
    if not ok:
        print("no successful trials")
        return
    llm = [r["llm_time_s"] for r in ok]
    wall = [r["wall_s"] for r in ok]
    rest = [max(0.0, w - l) for w, l in zip(wall, llm)]
    calls = [r["llm_calls"] for r in ok]
    per_call = [r["mean_latency_s"] for r in ok if r.get("mean_latency_s")]
    tokens = [r["output_tokens"] for r in ok if r.get("output_tokens")]

    def med(xs):
        return f"{statistics.median(xs):.2f}"

    print(f"{len(ok)} successful trials")
    print(f"  LLM calls per trial        median {statistics.median(calls)}  (max {max(calls)})")
    print(f"  seconds per LLM call       median {med(per_call)}")
    print(f"  output tokens per trial    median {statistics.median(tokens):.0f}" if tokens else "")
    print(f"  wall time per trial        median {med(wall)} s")
    print(f"     of which the model      median {med(llm)} s  ({100 * statistics.median(llm) / statistics.median(wall):.0f}%)")
    print(f"     of which everything else median {med(rest)} s  (search, Z3, the leaf assist)")
    cert = [r["certificate"]["coq"]["seconds"] for r in ok
            if r.get("certificate") and r["certificate"].get("coq")]
    if cert:
        print(f"  Coq certificate (after)    median {med(cert)} s for the whole derivation")
    lean = [r["certificate"]["lean"]["seconds"] for r in ok
            if r.get("certificate") and r["certificate"].get("lean")]
    if lean:
        print(f"  Lean certificate (after)   median {med(lean)} s for the whole derivation")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "benchmarks/results/reliability/*.jsonl")
