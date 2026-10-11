import sys, os, collections, time
sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
import z3
from benchmarks.datasets.he_specs import SPECS
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.llm.parser import parse_expr
from FormalLLM.verification import z3_backend as zb
spec = parse_spec(SPECS["HumanEval/13"]["spec"])
eng = RefinementEngine()
R = parse_expr("g > 0 && exists (k:int) a = g * k && exists (l:int) b = g * l")
p2 = eng.apply(spec, "sequential", {"intermediate": R}).by_role()["part2"]
law = eng.laws["assignment"]()
ob = law.apply(p2, {"variable": "x", "expr": parse_expr("g * k")}).obligations[0]
counts = collections.Counter()
t0 = time.time()
for seed in [None] + list(range(1, 41)):
    solver, tr, res = zb._attempt(ob, 1500, seed)
    counts[str(res)] += 1
    if res == z3.unsat:
        print("UNSAT (claimed proof) with seed", seed)
print(dict(counts), round(time.time() - t0, 1), "s")
