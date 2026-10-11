import sys, time, os
sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
from benchmarks.cases import CASES
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.agent import assist
from FormalLLM.llm.parser import parse_expr
n = [0]
orig = RefinementEngine.apply
def counting(self, *a, **k):
    n[0] += 1
    return orig(self, *a, **k)
case = [c for c in CASES if c["id"] == "D1-intdiv"][0]
eng = RefinementEngine()
spec = parse_spec(case["spec"])
for inv in ("q * d + r = n && r >= 0 && r <= n", "q * d + r = n && r >= 0"):
    res = eng.apply(spec, "initialised_iteration", {k: parse_expr(v) for k, v in {"invariant": inv, "guard": "r >= d", "variant": "r"}.items()})
    for role, s in res.by_role().items():
        RefinementEngine.apply = counting; n[0] = 0
        t = time.time(); r = assist.LeafSolver(eng).solve_pair(s)
        RefinementEngine.apply = orig
        print(inv[:32], role, "pair queries", n[0], "secs", round(time.time() - t, 2), "found" if r else "NONE")
hard = parse_spec("Frame: a:int, b:int, c:int.\nPrecondition: (N:int)(M:int) := true.\nPostcondition: (N:int)(M:int) := a*a + b*b = c*c + 7 /\ a > N /\ b > M /\ c > N + M.")
for cap in (4000, 1000):
    t = time.time(); r = assist.LeafSolver(eng, pair_queries=cap).solve_pair(hard)
    print("no-solution node, cap", cap, "secs", round(time.time() - t, 1), "found" if r else "NONE")
