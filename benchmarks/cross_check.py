"""Do the *proved* programs also *run* correctly?  A model-free cross-check of stored studies.

A refinement trial succeeds when every step is proved. That is a statement about all inputs, but
only for the specification as written and only over exact numbers. This script closes the loop
the other way: it takes every successful derivation stored in a reliability result file, runs
the emitted Python on concrete inputs, and asks two independent questions of each output:

  spec      does (input, output) satisfy the case's own formal precondition/postcondition?
            (evaluated by FormalLLM/lspec/evaluator.py on Python numbers, with no tolerance)
  baseline  does it pass the hard-coded check the direct-code baseline arm uses?
            (benchmarks/baseline_cases.py, which has a 1e-9 tolerance for floats)

No model and no network are needed. A program that is proved correct over the reals can still
fail here when the Python floats round (``x*x <= N`` off by one ulp): that is a finding, not noise.

    python benchmarks/cross_check.py "benchmarks/results/reliability/v6_relaxed_assist_*.jsonl"
    python benchmarks/cross_check.py "benchmarks/results/reliability/v7_*.jsonl" --random 200
"""
import argparse
import collections
import glob
import json
import os
import random
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from cases import CASES_BY_ID                       # noqa: E402
from baseline_cases import BASELINE                 # noqa: E402
from FormalLLM.lspec.parser import parse_spec       # noqa: E402
from FormalLLM.lspec import evaluator               # noqa: E402


class StepLimit(Exception):
    """The program ran longer than the step budget (treated as non-termination)."""


def run_limited(code: str, inputs: dict, outputs, max_events: int = 4_000_000):
    """Run emitted Python on ``inputs`` and return {output: value}; raise StepLimit on a runaway loop.

    A trace hook counts events instead of using a signal or a thread, so it behaves the same on
    Windows and Linux.
    """
    namespace = dict(inputs)
    count = 0

    def tracer(frame, event, arg):
        nonlocal count
        count += 1
        if count > max_events:
            raise StepLimit()
        return tracer

    compiled = compile(code, "<derived program>", "exec")
    sys.settrace(tracer)
    try:
        exec(compiled, {"__builtins__": {}}, namespace)
    finally:
        sys.settrace(None)
    return {name: namespace.get(name) for name in outputs}


def signature_params(signature: str):
    inside = signature[signature.index("(") + 1: signature.rindex(")")]
    return [part.split(":")[0].strip() for part in inside.split(",") if part.strip()]


def frame_order(spec_text: str):
    """Frame variables in the order the specification declares them (``Frame: s, d.``)."""
    line = re.search(r"Frame:\s*(.*?)\.\s*(?:\n|$)", spec_text).group(1)
    return [part.split(":")[0].strip() for part in line.split(",") if part.strip()]


def pinned_initials(spec_text: str, params, frame):
    """Start values the precondition itself fixes for frame variables the baseline does not pass in.

    ``Precondition: (N:int)(i:int) := N >= 0 /\\ i = 0.`` says ``i`` starts at 0, so a program that
    reads ``i`` (or a spec check that evaluates the precondition) needs it set. Only top-level
    conjuncts of the form ``name = integer`` are used; anything else is left for the program to set.
    """
    line = re.search(r"Precondition:[^\n]*", spec_text)
    if not line or ":=" not in line.group(0):
        return {}
    body = line.group(0).split(":=", 1)[1].strip().rstrip(".")
    pinned = {}
    for conjunct in body.split("/\\"):
        found = re.fullmatch(r"\s*(\w+)\s*=\s*(-?\d+)\s*", conjunct)
        if found and found.group(1) in frame and found.group(1) not in params:
            pinned[found.group(1)] = int(found.group(2))
    return pinned


def random_inputs(case_id: str, count: int, rng: random.Random):
    """Extra inputs beyond the baseline's, only for the problems where a range is obvious."""
    if case_id == "C5-sqrt-paper":
        return [(round(rng.uniform(0, 400), 3), round(rng.uniform(0.01, 1.0), 3)) for _ in range(count)]
    if case_id == "D1-intdiv":
        return [(rng.randint(0, 5000), rng.randint(1, 200)) for _ in range(count)]
    return []


def check_program(case_id: str, code: str, extra: int, rng: random.Random):
    """Run one derived program on every input; return (n, spec_failures, baseline_failures, runaways)."""
    case, base = CASES_BY_ID[case_id], BASELINE[case_id]
    spec = parse_spec(case["spec"])
    params, frame = signature_params(base["signature"]), frame_order(case["spec"])
    pinned = pinned_initials(case["spec"], params, frame)
    inputs = list(base["inputs"]) + random_inputs(case_id, extra, rng)
    spec_bad, base_bad, runaway = [], [], []
    for args in inputs:
        env = dict(zip(params, args))
        for name, start in pinned.items():
            env.setdefault(name, start)
        try:
            out = run_limited(code, env, frame)
        except StepLimit:
            runaway.append(args)
            continue
        except Exception as error:                          # e.g. a name read before it is set
            crash = f"the program crashed: {type(error).__name__}: {error}"
            spec_bad.append((args, None, crash))
            base_bad.append((args, crash))
            continue
        value = out[frame[0]] if len(frame) == 1 else tuple(out[name] for name in frame)
        why = evaluator.check_specification(spec, env, out)
        if why:
            spec_bad.append((args, value, why))
        try:
            if not base["check"](args, value):
                base_bad.append((args, value))
        except Exception as error:                          # a check that cannot judge counts as a failure
            base_bad.append((args, f"{type(error).__name__}: {error}"))
    return len(inputs), spec_bad, base_bad, runaway


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pattern", help="glob of reliability result files (.jsonl)")
    ap.add_argument("--random", type=int, default=0, metavar="N",
                    help="also try N random inputs (square root and integer division only)")
    ap.add_argument("--seed", type=int, default=20261004)
    ap.add_argument("--show", type=int, default=3, help="how many failing inputs to print per program")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    seen = collections.OrderedDict()                       # (case, code) -> number of derivations that ended in it
    for path in sorted(glob.glob(args.pattern)):
        for line in open(path, encoding="utf8"):
            if not line.strip():
                continue
            rec = json.loads(line)
            if rec.get("outcome") == "SUCCESS" and rec.get("program_python") and rec["case_id"] in BASELINE:
                key = (rec["case_id"], rec["program_python"])
                seen[key] = seen.get(key, 0) + 1
    if not seen:
        raise SystemExit("no successful derivations with a Python program found in " + args.pattern)

    per_case = collections.OrderedDict()
    for (case_id, code), times in seen.items():
        n, spec_bad, base_bad, runaway = check_program(case_id, code, args.random, rng)
        agg = per_case.setdefault(case_id, dict(derivations=0, programs=0, inputs=n, spec_ok=0, base_ok=0,
                                                 run_ok=0))
        agg["derivations"] += times
        agg["programs"] += 1
        agg["spec_ok"] += times * (not spec_bad and not runaway)
        agg["base_ok"] += times * (not base_bad and not runaway)
        agg["run_ok"] += times * (not runaway)
        flag = "ok " if not (spec_bad or base_bad or runaway) else "BAD"
        print(f"[{flag}] {case_id:20s} x{times:<3d} {n} inputs | spec fails {len(spec_bad)}, "
              f"baseline-check fails {len(base_bad)}, non-terminating {len(runaway)}")
        print("      " + code.strip().replace("\n", "\n      "))
        for item in spec_bad[:args.show]:
            print("      spec:", item)
        for item in base_bad[:args.show]:
            print("      baseline:", item)
        for item in runaway[:args.show]:
            print("      runaway:", item)

    print("\n==== per case (counted per derivation, not per distinct program) ====")
    print(f"{'case':20s} {'derivations':>11s} {'distinct programs':>17s} {'inputs':>7s} {'pass spec':>10s} {'pass baseline':>14s}")
    for case_id, a in per_case.items():
        print(f"{case_id:20s} {a['derivations']:>11d} {a['programs']:>17d} {a['inputs']:>7d} "
              f"{a['spec_ok']:>10d} {a['base_ok']:>14d}")
    if "A4-impossible" in per_case:
        print("\nA4-impossible is a negative control: no derivation of it should exist. "
              "Any row above for it means the system 'proved' an unsatisfiable specification.")


if __name__ == "__main__":
    main()
