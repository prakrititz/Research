import sys, time
sys.path.insert(0, '.')
from benchmarks.cases import CASES
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.verification.backends import get_backend
from FormalLLM.agent.assist import LeafSolver
from FormalLLM.llm.parser import parse_expr

case = [c for c in CASES if c["id"] == "D1-intdiv"][0]
spec = parse_spec(case["spec"])
eng = RefinementEngine(backend=get_backend("z3"))
for law, params in [("initialised_iteration", {"invariant": "q * d + r = n && r >= 0 && r <= n", "guard": "r >= d", "variant": "r"}),
                    ("initialised_iteration", {"invariant": "q * d + r = n && r >= 0", "guard": "r >= d", "variant": "r"})]:
    p = {k: parse_expr(v) for k, v in params.items()}
    try:
        res = eng.apply(spec, law, p)
    except Exception as e:
        print("REJECT", type(e).__name__, str(e)[:600]); continue
    print("accepted", params["invariant"])
    for s in res.sub_specs:
        t = time.time()
        r = LeafSolver(eng).solve(s)
        print("  sub ->", None if r is None else r[:2], round(time.time() - t, 1))
