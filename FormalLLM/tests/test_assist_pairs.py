"""The leaf assist can solve an equation for a variable and close a two-variable set-up by itself.

Both additions only *propose*: every step still goes through the engine and the prover, so these
tests check that the right steps are found, that nothing unproved is returned, and that the
refiner records an assist-made split exactly like a model's (so a certificate covers it).
"""
import json
import time

from FormalLLM.agent.assist import LeafSolver, candidate_expressions, solved_for
from FormalLLM.agent.refiner import AutomatedRefiner
from FormalLLM.llm import spec_render as sr
from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm.provider import MockProvider
from FormalLLM.lpl.typed_python import python_for
from FormalLLM.lspec import evaluator
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.verification.certify import derivation_obligations

DIVISION = (
    "Frame: q:int, r:int.\n"
    "Precondition: (n:int)(d:int) := n >= 0 /\\ d > 0.\n"
    "Postcondition: (n:int)(d:int) := q*d + r = n /\\ r >= 0 /\\ r < d."
)
LOOP = {"invariant": "q*d + r = n && r >= 0", "guard": "r >= d", "variant": "r"}


def loop_children():
    engine = RefinementEngine()
    result = engine.apply(parse_spec(DIVISION), "initialised_iteration",
                          {k: parse_expr(v) for k, v in LOOP.items()})
    return engine, result.by_role()


def solved(text, variable):
    spec = parse_spec("Frame: x:int, y:int.\nPrecondition: (a:int)(b:int) := true.\n"
                      f"Postcondition: (a:int)(b:int) := {text}.")
    return solved_for(spec, variable)


# --- solving an equation for one variable -------------------------------------------------

def test_an_equation_is_solved_for_the_variable_it_mentions_once():
    spec = parse_spec(DIVISION)
    assert solved_for(spec, "r") == ["n - q * d"]


def test_a_product_is_not_undone():
    assert solved_for(parse_spec(DIVISION), "q") == []            # q * d = n - r would need a division


def test_either_side_of_the_equation_and_subtraction_and_negation():
    assert solved("a = x + b", "x") == ["a - b"]
    assert solved("x - b = a", "x") == ["a + b"]
    assert solved("b - x = a", "x") == ["b - a"]
    assert solved("(-x) = a", "x") == ["-a"]


def test_only_equations_with_one_occurrence_and_only_top_level_conjuncts_are_used():
    assert solved("x + x = a", "x") == []
    assert solved("x = a \\/ x = b", "x") == []
    assert solved("x > a", "x") == []
    assert solved("x = a /\\ (y = x + 1 \\/ b = 0)", "x") == ["a"]       # the disjunction is not mined
    assert solved("x = a /\\ y = x + 1", "x") == ["a", "y - 1"]          # both conjuncts are equations


def test_the_solved_expression_comes_after_the_plain_families_so_the_plainer_program_wins():
    cands = candidate_expressions(parse_spec(DIVISION), "r")
    assert "n - q * d" in cands
    assert cands.index("r - d") < cands.index("n - q * d")
    assert cands.index("n") < cands.index("n - q * d")


def test_the_step_a_model_could_not_find_is_now_a_one_line_goal():
    # what remains after q := 0 and before the remainder is set: this is where trials ran out of budget
    leaf = parse_spec(
        "Frame: q:int, r:int.\n"
        "Precondition: (n:int)(d:int) := n >= 0 /\\ d > 0 /\\ q*d <= n /\\ q >= 0.\n"
        "Postcondition: (n:int)(d:int) := q*d + r = n /\\ r >= 0 /\\ r <= n.")
    law, params, _ = LeafSolver(RefinementEngine()).solve(leaf)
    assert (law, params["variable"], sr.render_expr(params["expr"])) == ("assignment", "r", "n - q * d")


# --- two assignments in a row ---------------------------------------------------------------

def test_the_division_set_up_and_body_are_each_closed_by_two_assignments():
    engine, roles = loop_children()
    expected = {"init": [("r", "n"), ("q", "0")], "body": [("r", "r - d"), ("q", "q + 1")]}
    for role, steps in expected.items():
        solver = LeafSolver(engine)
        law, params, result = solver.solve(roles[role])
        assert law == "sequential" and "intermediate" in params
        assert [(p["variable"], sr.render_expr(p["expr"])) for _, p in
                (solver.plan["part1"], solver.plan["part2"])] == steps
        # each part is really finished by its step: the engine accepts them again
        for part_role, sub_spec in result.by_role().items():
            step_law, step_params = solver.plan[part_role]
            assert engine.apply(sub_spec, step_law, step_params).program is not None


def test_a_single_assignment_leaves_no_plan():
    solver = LeafSolver(RefinementEngine())
    spec = parse_spec("Frame: x.\nPrecondition: (N:int) := N >= 0.\nPostcondition: (N:int) := x = N + 1.")
    law, _, _ = solver.solve(spec)
    assert law == "assignment" and solver.plan is None


def test_nothing_unproved_is_returned():
    both = parse_spec("Frame: a:int, b:int.\nPrecondition: (N:int) := true.\n"
                      "Postcondition: (N:int) := a > N /\\ a < N /\\ b = 0.")
    assert LeafSolver(RefinementEngine(), pair_seconds=1.0).solve(both) is None


def test_three_assignments_are_out_of_reach_and_the_search_gives_up_quickly():
    spec = parse_spec("Frame: a:int, b:int, c:int.\nPrecondition: (N:int) := true.\n"
                      "Postcondition: (N:int) := a = N /\\ b = N + 1 /\\ c = N + 2.")
    started = time.monotonic()
    assert LeafSolver(RefinementEngine(), pair_seconds=2.0).solve(spec) is None
    assert time.monotonic() - started < 10


def test_the_search_stops_at_its_time_limit():
    spec = parse_spec("Frame: a:int, b:int.\nPrecondition: (N:int)(M:int) := true.\n"
                      "Postcondition: (N:int)(M:int) := a*a + b*b = 7 /\\ a > N /\\ b > M.")
    started = time.monotonic()
    assert LeafSolver(RefinementEngine(), pair_seconds=0.5).solve(spec) is None
    assert time.monotonic() - started < 6


def test_a_one_variable_frame_never_searches_for_pairs():
    spec = parse_spec("Frame: x:int.\nPrecondition: (N:int) := true.\nPostcondition: (N:int) := x > N /\\ x < N.")
    solver = LeafSolver(RefinementEngine(), pair_seconds=30.0)
    started = time.monotonic()
    assert solver.solve(spec) is None
    assert time.monotonic() - started < 5          # no pair search: it would have run to 30 s


# --- inside the refiner ---------------------------------------------------------------------

def run_division(assist):
    reply = json.dumps({"law": "initialised_iteration", "parameters": LOOP})
    llm = MockProvider([reply])
    engine = RefinementEngine()
    refiner = AutomatedRefiner(engine, llm, max_retries=2, assist=assist)
    graph = RefinementGraph(parse_spec(DIVISION))
    try:
        refiner.refine_node(graph, graph.root_id)
    except Exception:
        pass                                   # without the assist the scripted model has nothing for the parts
    return engine, refiner, graph, llm


def test_the_model_only_chooses_the_loop_and_the_assist_finishes_the_derivation():
    engine, refiner, graph, llm = run_division(assist=True)
    assert graph.is_complete(graph.root_id)
    assert len(llm.prompts_received) == 1
    assert refiner.assist_discharges == 6                  # two split nodes and the four assignments below them
    spec = graph.nodes[graph.root_id].specification
    code = python_for(graph.reconstruct_program(), spec)
    for n, d in [(0, 1), (7, 3), (3, 7), (100, 7), (12345, 11), (10, 10), (1, 1000)]:
        env = {"n": n, "d": d}
        out = dict(env)
        exec(code, {"__builtins__": {}}, out)
        assert evaluator.check_specification(spec, env, {"q": out["q"], "r": out["r"]}) is None, (n, d)


def test_without_the_assist_the_same_script_does_not_finish():
    _, refiner, graph, llm = run_division(assist=False)
    assert not graph.is_complete(graph.root_id)
    assert refiner.assist_discharges == 0


def test_an_assist_made_split_is_in_the_derivation_the_certificate_covers():
    engine, _, graph, _ = run_division(assist=True)
    laws = sorted(item["law"] for item in derivation_obligations(graph, engine))
    # the loop, then the four assignments that the assist chose; the splits themselves carry no obligation
    assert laws == ["assignment"] * 4 + ["initialised_iteration"]
    sources = [getattr(a, "source", None) for a in graph.attempts.values()]
    assert sources.count("assist") == 6


def test_a_pair_whose_second_value_is_an_equation_with_three_names_is_found():
    spec = parse_spec("Frame: a:int, b:int.\nPrecondition: (N:int)(M:int)(K:int) := true.\n"
                      "Postcondition: (N:int)(M:int)(K:int) := a = N /\\ a + b = M + K.")
    solver = LeafSolver(RefinementEngine())
    law, params, result = solver.solve(spec)
    assert law == "sequential" and set(solver.plan) == {"part1", "part2"}
    steps = {role: (p["variable"], sr.render_expr(p["expr"])) for role, (_, p) in solver.plan.items()}
    assert sorted(steps.values()) == [("a", "N"), ("b", "M + K - N")]


# --- the guesses are always checked by Z3 ----------------------------------------------------

class Tripwire:
    """Stands for Lean or Coq: far too slow to be asked about hundreds of guesses, so it must not be."""
    name = "tripwire"

    def __init__(self):
        self.calls = 0

    def verify(self, obligation, timeout_ms=None):
        self.calls += 1
        raise AssertionError("the assist asked the run's own backend to check a guess")


def test_guesses_are_checked_with_z3_whatever_backend_the_run_uses():
    _, roles = loop_children()
    tripwire = Tripwire()
    engine = RefinementEngine(backend=tripwire)
    for role in ("init", "body"):
        law, params, _ = LeafSolver(engine).solve(roles[role])
        assert law == "sequential" and "intermediate" in params
    law, _, _ = LeafSolver(engine).solve(
        parse_spec("Frame: x.\nPrecondition: (N:int) := N >= 0.\nPostcondition: (N:int) := x = N + 1."))
    assert law == "assignment"
    assert tripwire.calls == 0


def test_the_screening_engine_keeps_the_runs_laws_and_feasibility_setting():
    engine = RefinementEngine(backend=Tripwire(), check_feasibility=False)
    solver = LeafSolver(engine)
    assert solver.screen is not engine
    assert solver.screen.check_feasibility is False
    assert solver.screen.laws == engine.laws
    plain = RefinementEngine()
    assert LeafSolver(plain).screen is plain      # a Z3 run needs no second engine


# --- the search is limited by work, not by time ----------------------------------------------

def test_the_pair_search_does_not_depend_on_the_wall_clock(monkeypatch):
    """Replaying stored division trials with the old 4-second limit shrunk to 0.2 s (a machine about twenty
    times slower) turned a 2-call success into a 30-call failure: the search's outcome depended on the clock.
    It is now limited by prover queries: with the wall-clock safety net out of the way, a clock running 1000x too fast
    must not change the answer (the earlier 10x version failed on a busy machine once the 20 s net was reached)."""
    import FormalLLM.agent.assist as assist_module
    engine, parts = loop_children()
    real = time.monotonic
    monkeypatch.setattr(assist_module.time, "monotonic", lambda: real() * 1000.0)
    solver = LeafSolver(engine, pair_seconds=1e12)        # the safety net out of the way: only queries limit it
    assert solver.solve(parts["body"].spec if hasattr(parts["body"], "spec") else parts["body"]) is not None


def test_a_query_budget_stops_the_pair_search_and_a_larger_one_finds_it():
    engine, parts = loop_children()
    body = parts["body"].spec if hasattr(parts["body"], "spec") else parts["body"]
    assert LeafSolver(engine, pair_queries=5).solve_pair(body) is None
    assert LeafSolver(engine).solve_pair(body) is not None
