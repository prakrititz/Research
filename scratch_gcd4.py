"""Can the assist (wrongly) close the gcd sub-problem [R, Q] that the live run closed with x := g * k?"""
import os
import sys
import time

sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
import z3  # noqa: E402

from benchmarks.datasets.he_specs import SPECS  # noqa: E402
from FormalLLM.agent.assist import LeafSolver  # noqa: E402
from FormalLLM.llm.parser import parse_expr  # noqa: E402
from FormalLLM.lspec.parser import parse_spec  # noqa: E402
from FormalLLM.refinement.engine import RefinementEngine  # noqa: E402
from FormalLLM.verification import z3_backend as zb  # noqa: E402

print("z3", z3.get_version_string(), flush=True)
spec = parse_spec(SPECS["HumanEval/13"]["spec"])
eng = RefinementEngine()
R = parse_expr("g > 0 && exists (k:int) a = g * k && exists (l:int) b = g * l")
p2 = eng.apply(spec, "sequential", {"intermediate": R}).by_role()["part2"]

# record every Z3 verdict the assist gets, so a wrong "proved" can be caught with its formula
original = zb._attempt
log = []


def recording(obligation, timeout_ms, seed=None):
    solver, translator, result = original(obligation, timeout_ms, seed)
    log.append(str(result))
    if result == z3.unsat:
        with open("scratch_gcd4_unsat.smt2", "a", encoding="utf8") as handle:
            handle.write(f"; seed {seed} timeout {timeout_ms}\n{solver.to_smt2()}\n")
    return solver, translator, result


zb._attempt = recording
for trial in range(4):
    log.clear()
    started = time.time()
    found = LeafSolver(eng).solve(p2)
    verdicts = {v: log.count(v) for v in set(log)}
    print(f"trial {trial}: {None if found is None else (found[0], found[1])}  "
          f"{time.time() - started:.0f} s  verdicts {verdicts}", flush=True)
