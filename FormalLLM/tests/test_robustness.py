"""Robustness fixes found by running the paper's square-root example end to end.

Each test names the failure it prevents. The numbers in the docstrings come from
a real run of gpt-oss-120b on the paper's example (Reading Material/12, section 6).
"""
import json

import pytest

from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
from FormalLLM.llm.parser import parse_expr, parse_llm_response, parse_parameters_response
from FormalLLM.llm.provider import LLMBudgetExhausted, LLMProvider, MockProvider
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.refinement.graph.status import AttemptStatus
from FormalLLM.llm import spec_render as sr

SQRT = (
    "Frame: x.\n"
    "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0.\n"
    "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e)."
)
SIMPLE = "Precondition: (x:int) := x > 5.\nPostcondition: (x:int) := x > 0."


def reply(law, **parameters):
    return json.dumps({"law": law, "parameters": parameters})


def no_feasibility_engine():
    """These tests exercise the feedback path *below an accepted step*. The paper's weak loop
    (Fig. 2's invariant) is now rejected up front by the feasibility check, so the engine is
    built without it; tests/test_repair.py and the tests at the end of this file cover that check."""
    return RefinementEngine(check_feasibility=False)


# --- G16: the budget stop must not be swallowed -----------------------------

class OutOfBudget(LLMProvider):
    def generate(self, prompt, max_tokens=None):
        raise LLMBudgetExhausted("LLM call budget of 0 exhausted")


def test_budget_exhaustion_propagates_instead_of_becoming_a_failed_attempt():
    """A run that stopped on its budget used to be reported EXHAUSTED, with 23
    fake 'LLM call budget exhausted' attempts in the graph."""
    graph = RefinementGraph(parse_spec(SIMPLE))
    refiner = AutomatedRefiner(RefinementEngine(), OutOfBudget(), max_retries=3)
    with pytest.raises(LLMBudgetExhausted):
        refiner.refine_node(graph, graph.root_id)
    assert not graph.attempts, "the budget stop must not be recorded as an attempt"


# --- G17: reply keys -------------------------------------------------------

def test_single_letter_keys_are_accepted_for_loop_parameters():
    """gpt-oss-120b sent {"I":..., "G":..., "V":...} and a correct loop was discarded."""
    params = parse_parameters_response(
        json.dumps({"parameters": {"I": "x*x <= N && x >= 0", "G": "(x+e)*(x+e) <= N",
                                   "V": "N - x*x"}}),
        "initialised_iteration")
    assert set(params) == {"invariant", "guard", "variant"}


def test_parameters_beside_the_law_name_are_accepted():
    law, params = parse_llm_response(json.dumps({"law": "alternation", "guard": "x > 0"}))
    assert law == "alternation" and "guard" in params


def test_numeric_parameter_values_are_accepted():
    params = parse_parameters_response(
        json.dumps({"parameters": {"variable": "x", "expr": 0}}), "assignment")
    assert sr.render_expr(params["expr"]) == "0"


def test_unrecognised_keys_are_reported_not_replaced_by_a_default():
    """alternation's guard defaults to `true`; a misspelt key must not hide behind it."""
    with pytest.raises(ValueError, match="unrecognised parameter key"):
        parse_parameters_response(json.dumps({"parameters": {"condition_test": "x > 0"}}),
                                  "alternation")


# --- negation scope ---------------------------------------------------------

def test_negation_binds_to_its_own_operand():
    """`!(x < 0) && y > 1` was parsed as `~((x < 0) /\\ (y > 1))`: 'not both'."""
    top = parse_expr("!(x < 0) && y > 1")
    assert top.op == "/\\"
    assert top.left.op == "~"


def test_double_negation_and_not_keyword():
    assert parse_expr("!!(a > 1)").op == "~"
    assert parse_expr("not (a > 1) and b > 2").op == "/\\"


# --- credit assignment ------------------------------------------------------

def _weak_loop_script():
    weak = reply("initialised_iteration", invariant="x * x <= N", guard="N >= (x + e) * (x + e)",
                 variant="N - x * x")
    return [weak,
            reply("assignment", variable="x", expr="0"),
            reply("assignment", variable="x", expr="x + e"),       # body: rejected, x may be negative
            reply("assignment", variable="x", expr="x + e / 2")]   # body: rejected as well


def test_parent_is_told_what_failed_below_it():
    """The parent used to hear only "Child node 'N2' exhausted all options"."""
    llm = MockProvider(_weak_loop_script() + [reply("skip")])
    refiner = AutomatedRefiner(no_feasibility_engine(), llm, max_retries=2)
    graph = RefinementGraph(parse_spec(SQRT))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)

    # prompts_received: 0 root, 1 init, 2 body#1, 3 body#2, 4 root retry
    root_retry = llm.prompts_received[4]
    assert "Sub-specification 'body'" in root_retry
    assert "Counterexample (these values satisfy the assumptions" in root_retry
    assert "usually comes from the parameters chosen at THIS step" in root_retry


def test_history_shows_parameters_as_formulas_not_dataclass_reprs():
    llm = MockProvider(_weak_loop_script() + [reply("skip")])
    refiner = AutomatedRefiner(no_feasibility_engine(), llm, max_retries=2)
    graph = RefinementGraph(parse_spec(SQRT))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)
    text = llm.prompts_received[4]
    assert "BinaryOp(" not in text and "Variable(" not in text
    assert "invariant = x * x <= N" in text


def test_the_failing_goal_conjunct_is_named():
    """A counterexample alone does not say which requirement it breaks."""
    llm = MockProvider(_weak_loop_script())
    refiner = AutomatedRefiner(no_feasibility_engine(), llm, max_retries=2)
    graph = RefinementGraph(parse_spec(SQRT))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)
    body_retry = llm.prompts_received[3]          # the body's second prompt
    assert "For these values the following part of the goal is false" in body_retry
    assert "V0" in body_retry


# --- wandering ----------------------------------------------------------------

def test_two_reshaping_steps_in_a_row_are_refused():
    """strengthen_post -> weaken_pre -> weaken_pre ... consumed 27 of 40 calls."""
    llm = MockProvider([
        reply("strengthen_post", intermediate_post="x > 3"),
        reply("weaken_pre", intermediate_pre="x > 4"),          # refused: chained
        reply("skip"),
    ])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3)
    graph = RefinementGraph(parse_spec(SIMPLE))
    assert refiner.refine_node(graph, graph.root_id) is True

    child = graph.nodes["N1"]
    statuses = [graph.attempts[a].status for a in child.attempts]
    assert statuses == [AttemptStatus.REJECTED, AttemptStatus.ACCEPTED]
    assert "Two specification-reshaping steps in a row" in graph.attempts[child.attempts[0]].counterexample
    assert "weaken_pre" in refiner.blacklisted_laws_per_node["N1"]


def test_a_reshaping_step_after_a_structural_one_is_allowed():
    llm = MockProvider([
        reply("sequential", intermediate="x > 3"),
        reply("weaken_pre", intermediate_pre="x > 4"),
        reply("skip"),
        reply("skip"),
    ])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3)
    graph = RefinementGraph(parse_spec(SIMPLE))
    # sequential -> [x > 5, x > 3] ; [x > 3, x > 0]. weaken_pre on the first is fine.
    refiner.refine_node(graph, graph.root_id)
    laws = [a.law for a in graph.attempts.values()]
    assert "weaken_pre" in laws
    assert all("reshaping" not in (a.counterexample or "") for a in graph.attempts.values())


def test_a_repeated_failed_proposal_is_turned_away_without_a_proof():
    spec = parse_spec("Precondition: (N:float) := N >= 0.\nPostcondition: (N:float) := x*x <= N.")
    llm = MockProvider([reply("assignment", variable="x", expr="100"),
                        reply("assignment", variable="x", expr="100"),
                        reply("assignment", variable="x", expr="0")])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3)
    graph = RefinementGraph(spec)
    assert refiner.refine_node(graph, graph.root_id) is True
    messages = [graph.attempts[a].counterexample or "" for a in graph.nodes[graph.root_id].attempts]
    assert "exactly the parameters of an earlier attempt" in messages[1]


# --- the assist's refuted update is not thrown away ---------------------------

def test_assist_near_miss_is_shown_to_the_model_and_kept_for_the_parent():
    """With the paper's Fig. 2 invariant the obvious body `x := x + e` fails. The assist
    found that counterexample and used to discard it; the model then wandered."""
    weak = reply("initialised_iteration", invariant="x * x <= N", guard="N >= (x + e) * (x + e)",
                 variant="N - (x + e) * (x + e)")
    llm = MockProvider([weak, reply("skip"), reply("skip"), reply("skip"), reply("skip")])
    refiner = AutomatedRefiner(no_feasibility_engine(), llm, max_retries=2, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)

    # the first prompt after the root's is the body's: it must already carry the near miss
    body_prompt = llm.prompts_received[1]
    assert "expr = x + e" in body_prompt
    assert "Counterexample (these values satisfy the assumptions" in body_prompt
    recorded = [a for a in graph.attempts.values() if getattr(a, "source", None) == "assist"
                and a.status == AttemptStatus.REJECTED]
    assert recorded, "the refuted candidate should be a recorded, rejected attempt"


def test_a_subtree_that_uses_up_its_calls_returns_to_its_parent():
    llm = MockProvider([reply("sequential", intermediate="x > 3")] * 6)
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, subtree_budget=0)
    graph = RefinementGraph(parse_spec(SIMPLE))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)
    # only the root ever called the model; its children gave up at once
    assert len(llm.prompts_received) == 3
    assert all(n.status.value in ("failed", "open", "delegated", "refining")
               for n in graph.nodes.values())


def test_the_subtree_cap_does_not_apply_to_the_root():
    llm = MockProvider([reply("skip")])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=2, subtree_budget=0)
    graph = RefinementGraph(parse_spec(SIMPLE))
    assert refiner.refine_node(graph, graph.root_id) is True


def test_the_cap_binds_a_long_chain_of_nodes_that_are_each_under_it():
    """A chain of structural steps, one call per node, hid a doomed branch from the old
    per-node check: no single node ever exceeded its allowance."""
    chain = [reply("sequential", intermediate=f"x > {5 - 0.01 * (i + 1):.2f}") for i in range(60)]
    llm = MockProvider(chain)
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=1, max_depth=100, subtree_budget=5)
    graph = RefinementGraph(parse_spec(SIMPLE))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)
    # 1 call for the root, then the first child's subtree may use 5 before it is cut off
    assert len(llm.prompts_received) == 6


def test_a_cut_off_branch_is_reported_to_its_parent_not_swallowed_as_an_error():
    chain = [reply("sequential", intermediate=f"x > {5 - 0.01 * (i + 1):.2f}") for i in range(60)]
    llm = MockProvider(chain + [reply("skip")])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=2, max_depth=100, subtree_budget=3)
    graph = RefinementGraph(parse_spec(SIMPLE))
    try:
        refiner.refine_node(graph, graph.root_id)
    except RefinementExhausted:
        pass
    errors = [a for a in graph.attempts.values() if a.status == AttemptStatus.ERROR]
    assert not errors, [a.error_message for a in errors]


# --- an impossible set-up step is refused at once -------------------------------

def test_an_invariant_that_no_state_can_satisfy_is_rejected_immediately():
    """The failed trial's invariant contained the guard's own condition, so it is false on
    entry whenever N < e*e: no program can establish it, and 28 LLM calls were spent
    below the set-up node discovering that."""
    from FormalLLM.refinement.engine import VerificationError
    spec = parse_spec(SQRT)
    too_strong = parse_expr("x*x <= N && N - (x+e)*(x+e) >= 0 && N >= 0 && e > 0")
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(spec, "initialised_iteration", {
            "invariant": too_strong, "guard": parse_expr("N >= (x+e)*(x+e)"),
            "variant": parse_expr("N - x*x")})
    message = str(caught.value)
    assert "the set-up step must be possible" in message
    assert "Counterexample" in message


def test_good_invariants_pass_the_set_up_check():
    spec = parse_spec(SQRT)
    RefinementEngine().apply(spec, "initialised_iteration", {
        "invariant": parse_expr("x*x <= N && x >= 0"), "guard": parse_expr("N >= (x+e)*(x+e)"),
        "variant": parse_expr("N - x*x")})
    # the paper's weaker invariant is fine for set-up; only the body's feasibility depends on it
    RefinementEngine(check_feasibility=False).apply(spec, "initialised_iteration", {
        "invariant": parse_expr("x*x <= N"), "guard": parse_expr("N >= (x+e)*(x+e)"),
        "variant": parse_expr("N - x*x")})


def test_the_feasibility_checks_are_advisory_and_never_certified():
    """They are necessary conditions for refinability, not part of the law's soundness:
    one per sub-specification (set-up and body), kept apart from the law's own obligation."""
    spec = parse_spec(SQRT)
    result = RefinementEngine().apply(spec, "initialised_iteration", {
        "invariant": parse_expr("x*x <= N && x >= 0"), "guard": parse_expr("N >= (x+e)*(x+e)"),
        "variant": parse_expr("N - x*x")})
    assert len(result.advisory) == 2 and len(result.obligations) == 1


# --- every sub-specification must be feasible -----------------------------------

def test_a_loop_whose_body_cannot_proceed_is_rejected_at_once():
    """Fig. 2's invariant admits x = -1 with N = 1, e = 1. There the variant N - x*x is already 0
    and cannot decrease: no loop body exists, whatever the model writes below."""
    from FormalLLM.refinement.engine import VerificationError
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "initialised_iteration", {
            "invariant": parse_expr("x*x <= N"), "guard": parse_expr("N >= (x+e)*(x+e)"),
            "variant": parse_expr("N - x*x")})
    message = str(caught.value)
    assert "the loop body must be possible" in message
    assert "Counterexample" in message and "x = -1" in message
    assert "add a fact to the invariant that excludes them" in message


def test_an_invariant_that_restates_the_guard_is_rejected_at_once():
    """The failing run's invariant contained the guard's condition. In the else-branch it was
    refining, the set-up was fine -- but at N = (x+e)^2 the body cannot both keep the invariant and
    make progress, and 30 LLM calls were spent below it."""
    from FormalLLM.refinement.engine import VerificationError
    else_branch = parse_spec(
        "Frame: x.\n"
        "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0 /\\ x*x <= N /\\ N >= (x+e)*(x+e).\n"
        "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e).")
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(else_branch, "initialised_iteration", {
            "invariant": parse_expr("x*x <= N && N >= (x+e)*(x+e)"),
            "guard": parse_expr("N >= (x+e)*(x+e)"), "variant": parse_expr("N - (x+e)*(x+e)")})
    message = str(caught.value)
    assert "the loop body must be possible" in message and "Counterexample" in message


def test_an_intermediate_assertion_nothing_can_reach_is_rejected_at_once():
    from FormalLLM.refinement.engine import VerificationError
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "sequential", {"intermediate": parse_expr("x*x <= N - 1")})
    message = str(caught.value)
    assert "the first stage must be possible" in message and "N = 0" in message


def test_a_sound_split_is_not_refused():
    RefinementEngine().apply(parse_spec(SQRT), "sequential", {"intermediate": parse_expr("x*x <= N")})
    RefinementEngine().apply(parse_spec(SQRT), "alternation", {"guard": parse_expr("N >= 1")})


def test_the_feasibility_check_can_be_switched_off(monkeypatch):
    monkeypatch.setenv("FORMALLLM_FEASIBILITY", "0")
    engine = RefinementEngine()
    assert engine.check_feasibility is False
    engine.apply(parse_spec(SQRT), "sequential", {"intermediate": parse_expr("x*x <= N - 1")})


def test_specifications_about_the_previous_state_are_skipped_not_misjudged():
    """`x = x0 + 1` talks about the value before the step; the existential would have to be tied
    to it, so such a specification is not checked rather than wrongly refuted."""
    from FormalLLM.refinement.feasibility import feasibility_obligation
    spec = parse_spec("Frame: x.\nPrecondition: (N:int) := true.\nPostcondition: (N:int) := x = x0 + 1.")
    assert feasibility_obligation("sequential", "part1", spec) is None
