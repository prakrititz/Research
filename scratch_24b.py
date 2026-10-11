import sys, time, os
sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
from benchmarks.datasets.he_specs import SPECS
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError
from FormalLLM.llm.parser import parse_expr
spec = parse_spec(SPECS["HumanEval/24"]["spec"])
eng = RefinementEngine()
p = {"invariant": "1 <= r && r < n && forall (d:int) (! (d > r && d < n) || !(n = d * (n / d)))", "guard": "!(n = r * (n / r))", "variant": "r"}
body = eng.apply(spec, "initialised_iteration", {k: parse_expr(v) for k, v in p.items()}).by_role()["body"]
for expr in ("r - 1", "0", "1", "n", "r + 1"):
    for limit in (1500, 10000):
        t = time.time()
        try:
            eng.apply(body, "assignment", {"variable": "r", "expr": parse_expr(expr)}, timeout_ms=limit); v = "PROVED"
        except VerificationError as e:
            v = type(e).__name__ + ("" if "unknown" not in str(e) else " (unknown)")
        print(f"r := {expr:6s} limit {limit:5d} ms -> {v:30s} {time.time()-t:5.2f} s")
