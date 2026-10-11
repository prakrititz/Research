"""Diagnostic for one unexplained event: Z3 said "proved" for an obligation that has a counterexample.

What happened. In the stored pilot run ``benchmarks/results/datasets/he_refine_v7.jsonl`` row 21
(HumanEval/13, ``greatest_common_divisor``, repeat 0), the leaf helper closed a sub-goal with
``x := g * k`` and the prover accepted it. The question the prover was asked is

    a > 0 /\\ b > 0 /\\ g > 0 /\\ (exists k. a = g * k /\\ exists l. b = g * l)   =>   Q

where Q is the whole gcd postcondition. ``x`` does not occur in Q, so this is word for word the same
question as for ``x := 0`` or ``skip``, and it is false: a = b = 4, g = 1 satisfies the assumption and
breaks Q (4 divides both and is larger than g). Every offline repeat so far answered "counterexample"
or "out of time", never "proved" (in a Linux build of the same Z3 version: more than 1500 runs, with
fixed and with random time limits; a replay of rows 0 to 21 in one process did not reproduce it either).

What this script does. It rebuilds that obligation and asks Z3 the question again and again from a
fresh solver each time, exactly as ``FormalLLM/verification/z3_backend.py`` does for the helper's
candidates, and reports every answer. If Z3 ever answers "unsat" (= "proved") the script writes the
solver's state to ``probe_unsat_<n>.smt2`` (a standalone file that can be sent to the Z3 developers).

    python benchmarks/probe_wrong_step.py show             # print the obligation, ask once at 0.3 / 1.5 / 10 s
    python benchmarks/probe_wrong_step.py fuzz 600         # repeat for 600 s with random time limits
    python benchmarks/probe_wrong_step.py fuzz 600 5       # same, random generator seed 5 (use another one per terminal)
    python benchmarks/probe_wrong_step.py seeds 100        # 100 different Z3 random seeds, 1.5 s each

Run it on the machine that produced the stored run (the laptop), in several terminals at once to imitate
a busy machine; a result of "unsat" anywhere is the finding.
"""
import os
import random
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
os.environ.setdefault("FORMALLLM_STRICT_VARIANT", "0")

import z3  # noqa: E402
from benchmarks.datasets.he_specs import SPECS  # noqa: E402
from FormalLLM.lspec.parser import parse_spec  # noqa: E402
from FormalLLM.llm.parser import parse_expr  # noqa: E402
from FormalLLM.llm import spec_render as sr  # noqa: E402
from FormalLLM.refinement.laws.sequential import SequentialCompositionLaw  # noqa: E402
from FormalLLM.refinement.laws.assignment import AssignmentLaw  # noqa: E402
from FormalLLM.verification import z3_backend as zb  # noqa: E402

#: the model's intermediate assertion in the stored run (its second reply)
INTERMEDIATE = "g > 0 && exists (k:int) a = g * k && exists (l:int) b = g * l"


def build_obligation():
    spec = parse_spec(SPECS["HumanEval/13"]["spec"])
    split = SequentialCompositionLaw().apply(spec, {"intermediate": parse_expr(INTERMEDIATE)})
    second_half = split.sub_specs[1]
    step = AssignmentLaw().apply(second_half, {"variable": "x", "expr": parse_expr("g * k")})
    return step.obligations[0]


def ask(obligation, ms, seed=None):
    started = time.time()
    solver, _translator, result = zb._attempt(obligation, ms, seed)
    return solver, str(result), 1000 * (time.time() - started)


def report_unsat(obligation, solver, n, ms):
    path = f"probe_unsat_{os.getpid()}_{n}.smt2"
    try:
        with open(path, "w", encoding="utf8") as handle:
            handle.write(f"; Z3 {z3.get_version_string()}: answered unsat after run {n} with a {ms} ms limit\n")
            handle.write(solver.to_smt2())
    except Exception as error:  # pragma: no cover - never lose the finding because the dump failed
        path = f"(could not write the file: {error})"
    print(f"!!! UNSAT (= 'proved') on run {n}, time limit {ms} ms. Solver state saved to {path}", flush=True)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "show"
    obligation = build_obligation()
    print(f"Z3 {z3.get_version_string()} on Python {sys.version.split()[0]} ({sys.platform})")
    print("assumptions:", [sr.render_expr(a) for a in obligation.assumptions])
    print("goal       :", sr.render_expr(obligation.goal))
    counts = {}
    if mode == "show":
        for ms in (300, 1500, 10000):
            solver, result, took = ask(obligation, ms)
            print(f"time limit {ms:>6} ms: {result:<8} after {took:7.0f} ms")
            if result == "unsat":
                report_unsat(obligation, solver, 1, ms)
        return
    if mode == "seeds":
        runs = int(sys.argv[2]) if len(sys.argv) > 2 else 100
        for seed in range(runs):
            solver, result, took = ask(obligation, 1500, seed)
            counts[result] = counts.get(result, 0) + 1
            if result == "unsat":
                report_unsat(obligation, solver, seed, 1500)
        print("summary:", runs, "runs:", counts)
    elif mode == "fuzz":
        seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 600
        rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
        end, n = time.time() + seconds, 0
        while time.time() < end:
            ms = rng.choice([50, 100, 200, 300, 500, 800, 1000, 1500, 3000])
            solver, result, took = ask(obligation, ms)
            n += 1
            counts[result] = counts.get(result, 0) + 1
            if result == "unsat":
                report_unsat(obligation, solver, n, ms)
            if n % 100 == 0:
                print(f"{n} runs: {counts}", flush=True)
        print("summary:", n, "runs:", counts)
    else:
        sys.exit(__doc__)
    if "unsat" not in counts:
        print("No run answered 'unsat': Z3 never called the false obligation proved in these runs.")


if __name__ == "__main__":
    main()
