import sys, time, os
sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
from benchmarks.datasets.he_specs import SPECS
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.agent.assist import LeafSolver
from FormalLLM.llm.parser import parse_expr
spec = parse_spec(SPECS["HumanEval/24"]["spec"])
eng = RefinementEngine()
p = {"invariant": "1 <= r && r < n && forall (d:int) (! (d > r && d < n) || !(n = d * (n / d)))", "guard": "!(n = r * (n / r))", "variant": "r"}
res = eng.apply(spec, "initialised_iteration", {k: parse_expr(v) for k, v in p.items()})
for role, s in res.by_role().items():
    for trial in range(3):
        t = time.time(); r = LeafSolver(eng).solve(s)
        print(role, trial, None if r is None else (r[0], str(r[1].get("expr", r[1]))[:60]), round(time.time() - t, 2), "s")
