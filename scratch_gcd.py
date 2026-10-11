import sys, os
sys.path.insert(0, '.')
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
from benchmarks.datasets.he_specs import SPECS
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError
from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm import spec_render as sr
spec = parse_spec(SPECS["HumanEval/13"]["spec"])
eng = RefinementEngine()
R = parse_expr("g > 0 && exists (k:int) a = g * k && exists (l:int) b = g * l")
res = eng.apply(spec, "sequential", {"intermediate": R})
parts = res.by_role()
p2 = parts["part2"]
print("part2 pre :", sr.render_expr(p2.precondition.expr))
print("part2 post:", sr.render_expr(p2.postcondition.expr))
for law, params in [("assignment", {"variable": "x", "expr": parse_expr("g * k")}),
                    ("assignment", {"variable": "x", "expr": parse_expr("0")}),
                    ("skip", {})]:
    try:
        eng.apply(p2, law, params); print(law, params.get("expr"), "-> ACCEPTED")
    except VerificationError as e:
        print(law, "-> rejected:", type(e).__name__, " ".join(str(e).split())[:300])
