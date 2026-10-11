import sys, time
sys.path.insert(0, '.')
from benchmarks.cases import CASES
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.verification.backends import get_backend
from FormalLLM.agent import assist
from FormalLLM.llm.parser import parse_expr
import os
os.environ["FORMALLLM_STRICT_VARIANT"]="0"
case = [c for c in CASES if c["id"] == "D1-intdiv"][0]
spec = parse_spec(case["spec"])
eng = RefinementEngine(backend=get_backend("z3"))
n=[0]
orig=RefinementEngine.apply
def counting(self,*a,**k):
    n[0]+=1; return orig(self,*a,**k)
RefinementEngine.apply=counting
p = {k: parse_expr(v) for k, v in {"invariant": "q * d + r = n && r >= 0 && r <= n", "guard": "r >= d", "variant": "r"}.items()}
res = eng.apply(spec, "initialised_iteration", p)
for s in res.sub_specs:
    n[0]=0; t=time.time(); r=assist.LeafSolver(eng).solve(s); print("queries",n[0],"secs",round(time.time()-t,2), r[0] if r else None)
