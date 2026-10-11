"""The leaf assist closes one-line sub-goals; it must never accept anything unverified."""
import json

from FormalLLM.agent.assist import LeafSolver, candidate_expressions
from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
from FormalLLM.llm import spec_render as sr
from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm.provider import MockProvider
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.refinement.graph.graph import RefinementGraph

SQRT = (
    "Frame: x.\n"
    "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0.\n"
    "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e)."
)

LOOP = {"invariant": "x*x <= N && x >= 0", "guard": "N >= (x+e)*(x+e)", "variant": "N - x*x"}


def loop_children():
    engine = RefinementEngine()
    spec = parse_spec(SQRT)
    result = engine.apply(spec, "initialised_iteration", {k: parse_expr(v) for k, v in LOOP.items()})
    return engine, spec, result.by_role()


def test_the_loop_set_up_and_body_are_one_line_goals():
    engine, _, roles = loop_children()
    solver = LeafSolver(engine)
    law, params, _ = solver.solve(roles["init"])
    assert law == "assignment" and sr.render_expr(params["expr"]) == "0"
    law, params, _ = solver.solve(roles["body"])
    assert law == "assignment" and sr.render_expr(params["expr"]) == "x + e"


def test_the_creative_root_is_left_to_the_model():
    engine, spec, _ = loop_children()
    assert LeafSolver(engine).solve(spec) is None


def test_skip_is_tried_before_assignments():
    spec = parse_spec("Precondition: (x:int) := x > 5.\nPostcondition: (x:int) := x > 0.")
    law, _, _ = LeafSolver(RefinementEngine()).solve(spec)
    assert law == "skip"


def test_an_unsatisfiable_goal_is_never_closed():
    """Nothing is accepted without a proof: x > 0 and x < 0 has no solution."""
    spec = parse_spec("Frame: x.\nPrecondition: (N:int) := true.\nPostcondition: (N:int) := x > 0 /\\ x < 0.")
    assert LeafSolver(RefinementEngine()).solve(spec) is None


def test_candidates_come_from_the_specifications_own_names():
    spec = parse_spec(SQRT)
    cands = candidate_expressions(spec, "x")
    assert "0" in cands and "x + e" in cands
    assert all("sqrt" not in c for c in cands)


def test_refiner_with_assist_needs_one_llm_call_for_the_whole_derivation():
    reply = json.dumps({"law": "initialised_iteration", "parameters": LOOP})
    llm = MockProvider([reply])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=2, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    assert graph.is_complete(graph.root_id)
    assert len(llm.prompts_received) == 1
    assert refiner.assist_discharges == 2
    sources = [getattr(a, "source", None) for a in graph.attempts.values()]
    assert sources.count("assist") == 2


def test_assist_is_off_by_default():
    reply = json.dumps({"law": "initialised_iteration", "parameters": LOOP})
    llm = MockProvider([reply])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=2)
    graph = RefinementGraph(parse_spec(SQRT))
    try:
        refiner.refine_node(graph, graph.root_id)
    except RefinementExhausted:
        pass                            # the scripted model has nothing sensible for the children
    assert refiner.assist_discharges == 0
    assert len(llm.prompts_received) > 1   # the children went to the model
