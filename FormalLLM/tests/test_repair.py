"""Telling the step above what it left out.

Measured on the paper's square-root example (Reading Material/13): when the model's loop
invariant omitted `x >= 0`, the loop body `x := x + e` was refuted at x = -3. The model
answered the *body's* refutation with nested loops (it cannot change the invariant from
there), 16 calls were spent, and the failure that finally reached the parent was an
unrelated test of a different node. Each test below names one link of that chain.
"""
import json

import pytest

from FormalLLM.agent.assist import LeafSolver, candidate_facts
from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
from FormalLLM.llm.parser import parse_expr
from FormalLLM.llm.provider import MockProvider
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError
from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.refinement.graph.status import AttemptStatus, NodeStatus

SQRT = (
    "Frame: x.\n"
    "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0.\n"
    "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e)."
)
SIMPLE = "Precondition: (x:int) := x > 5.\nPostcondition: (x:int) := x > 0."

WEAK = {"invariant": "x * x <= N", "guard": "N >= (x + e) * (x + e)", "variant": "N - (x + e) * (x + e)"}
STRONG = {"invariant": "x * x <= N && x >= 0", "guard": "N >= (x + e) * (x + e)",
          "variant": "N - (x + e) * (x + e)"}


@pytest.fixture(autouse=True)
def relaxed_termination(monkeypatch):
    """The paper's Lemma 6.7 (variant decreases) -- the rule the reliability study runs under."""
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")


def reply(law, **parameters):
    return json.dumps({"law": law, "parameters": parameters})


def body_of(invariant):
    """The loop body's specification, built without the feasibility check so that bodies the
    check would refuse can still be handed to the leaf solver."""
    result = RefinementEngine(check_feasibility=False).apply(
        parse_spec(SQRT), "initialised_iteration", {k: parse_expr(v) for k, v in invariant.items()})
    return result.by_role()["body"]


# --- the diagnosis -----------------------------------------------------------

@pytest.mark.parametrize("variant", ["N - x*x", "N - (x+e)*(x+e)"])
def test_a_body_that_needs_a_sign_is_diagnosed(variant):
    solver = LeafSolver(RefinementEngine())
    body = body_of({"invariant": "x*x <= N", "guard": "N >= (x+e)*(x+e)", "variant": variant})
    assert solver.solve(body) is None
    law, parameters, _ = solver.near_miss
    assert law == "assignment" and parameters["variable"] == "x"
    assert solver.missing_fact == "x >= 0"


def test_a_sufficient_invariant_needs_no_diagnosis():
    solver = LeafSolver(RefinementEngine())
    assert solver.solve(body_of({**STRONG, "variant": "N - x*x"})) is not None
    assert solver.missing_fact is None


def test_no_fact_is_invented_where_none_would_help():
    """At the root `x := x + e` is wrong for a reason no extra assumption repairs."""
    solver = LeafSolver(RefinementEngine())
    assert solver.solve(parse_spec(SQRT)) is None
    assert solver.near_miss is not None and solver.missing_fact is None


def test_a_fact_that_contradicts_the_precondition_is_never_offered():
    """`x <= 0` would make anything follow from `x > 0`; that is vacuous, not a repair."""
    spec = parse_spec("Frame: x.\nPrecondition: (N:int) := x > 0.\nPostcondition: (N:int) := x < 0.")
    solver = LeafSolver(RefinementEngine())
    near_miss = ("assignment", {"variable": "x", "expr": parse_expr("x + 1")}, "")
    assert "x <= 0" in candidate_facts(spec, "x")
    assert solver.missing_fact_for(spec, near_miss) is None


def test_candidate_facts_are_about_the_frame_not_about_constants():
    facts = candidate_facts(parse_spec(SQRT), "x")
    assert facts[0] == "x >= 0"
    assert all(f.split()[0] == "x" for f in facts), "a step cannot add a fact about a constant"


# --- the search acts on it ---------------------------------------------------

def test_the_body_returns_to_its_parent_without_asking_the_model():
    llm = MockProvider([reply("initialised_iteration", **WEAK), reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    assert graph.is_complete(graph.root_id)
    # one call for the weak loop, one for the repaired loop: the body asked for none
    assert len(llm.prompts_received) == 2 and refiner.calls_made == 2

    retry = llm.prompts_received[1]
    assert "Its simplest candidate, x := x + e, is refuted" in retry
    assert "would be valid if the precondition of this sub-specification also guaranteed x >= 0" in retry
    assert "add x >= 0 to the invariant" in retry


def test_a_failing_trial_replayed_the_invariant_is_repaired_by_its_owner():
    """Root splits with `sequential`; the second half gets the weak loop. The half repairs its own
    invariant -- the root, whose R was fine, is not asked to change anything."""
    llm = MockProvider([reply("sequential", intermediate="x * x <= N"),
                        reply("initialised_iteration", **WEAK),
                        reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    assert graph.is_complete(graph.root_id)
    assert len(llm.prompts_received) == 3
    root_attempts = graph.nodes[graph.root_id].attempts
    assert len(root_attempts) == 1, "the root's step was never held against it"
    assert "add x >= 0 to the invariant" in llm.prompts_received[2]


def test_the_same_works_in_two_turn_mode():
    llm = MockProvider([reply("initialised_iteration"),          # law selection
                        reply("initialised_iteration", **WEAK),  # parameters
                        reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True, use_multi_turn=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    assert len(llm.prompts_received) == 3
    assert "add x >= 0 to the invariant" in llm.prompts_received[2]


def test_the_model_is_told_the_hint_not_a_generic_instruction():
    """The old trailer said 'strengthen the invariant' about *every* failure, including the one
    that needs a weaker invariant."""
    llm = MockProvider([reply("initialised_iteration", **WEAK), reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    refiner.refine_node(graph, graph.root_id)
    retry = llm.prompts_received[1]
    assert "Your parameters must be changed" not in retry


# --- a probe is evidence, not the model's mistake ------------------------------

def test_a_probe_is_labelled_as_the_systems_test():
    """When no missing fact explains the refutation the node goes to the model, whose history
    must not present the system's own quick test as a mistake of its own."""
    llm = MockProvider([reply("sequential", intermediate="x * x <= N"),
                        reply("skip"), reply("skip"), reply("skip"), reply("skip")])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=2, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    with pytest.raises(RefinementExhausted):
        refiner.refine_node(graph, graph.root_id)
    second_half_prompt = llm.prompts_received[1]
    assert "Not your proposal: the system tried this as a quick test" in second_half_prompt
    assert "expr = x + e" in second_half_prompt
    probes = [a for a in graph.attempts.values() if a.source == "assist" and a.status == AttemptStatus.REJECTED]
    assert probes and all(p.repair is None for p in probes)


def test_a_found_fact_is_recorded_on_the_probe():
    llm = MockProvider([reply("initialised_iteration", **WEAK), reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    refiner.refine_node(graph, graph.root_id)
    probes = [a for a in graph.attempts.values() if a.source == "assist" and a.repair]
    assert [p.repair for p in probes] == ["x >= 0"]


def test_attempts_default_to_the_models(tmp_path):
    graph = RefinementGraph(parse_spec(SIMPLE))
    attempt_id = graph.record_attempt(graph.root_id, "skip", {})
    assert graph.attempts[attempt_id].source == "model" and graph.attempts[attempt_id].repair is None


# --- the allowance belongs to a step, and the step may try again -----------------

def test_the_owner_of_an_exhausted_allowance_retries_instead_of_failing():
    chain = [reply("sequential", intermediate="x > 4"),     # root
             reply("skip"),                                  # first half
             reply("sequential", intermediate="x > 3"),     # second half starts a chain...
             reply("sequential", intermediate="x > 3.5"),
             reply("sequential", intermediate="x > 3.7"),
             reply("skip")]                                  # ...cut off; its retry settles it
    llm = MockProvider(chain)
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, max_depth=100, subtree_budget=3)
    graph = RefinementGraph(parse_spec(SIMPLE))
    assert refiner.refine_node(graph, graph.root_id) is True
    assert graph.is_complete(graph.root_id)
    assert len(llm.prompts_received) == 6

    second_half = [n for n in graph.nodes.values() if n.id == "N2"][0]
    statuses = [graph.attempts[a].status for a in second_half.attempts]
    assert statuses == [AttemptStatus.ABORTED, AttemptStatus.ACCEPTED]
    assert "used their allowance of 3 LLM calls" in graph.attempts[second_half.attempts[0]].error_message


def test_unwound_nodes_keep_the_chain_for_the_digest():
    """A node unwound by the cap is failed and its split aborted, so the failure digest can
    follow it down; left 'accepted', the chain would be invisible."""
    chain = [reply("sequential", intermediate="x > 4"), reply("skip"),
             reply("sequential", intermediate="x > 3"), reply("sequential", intermediate="x > 3.5"),
             reply("sequential", intermediate="x > 3.7"), reply("skip")]
    llm = MockProvider(chain)
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, max_depth=100, subtree_budget=3)
    graph = RefinementGraph(parse_spec(SIMPLE))
    refiner.refine_node(graph, graph.root_id)
    failed = [n for n in graph.nodes.values() if n.status == NodeStatus.FAILED]
    assert failed, "the cut-off descendants are recorded as failed"
    for node in failed:
        for attempt_id in node.attempts:
            attempt = graph.attempts[attempt_id]
            assert not (attempt.status == AttemptStatus.ACCEPTED and attempt.destination_roles)


# --- advice that fits the obligation -------------------------------------------

def test_the_set_up_check_asks_for_a_weaker_invariant():
    too_strong = parse_expr("x*x <= N && N - (x+e)*(x+e) >= 0 && N >= 0 && e > 0")
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "initialised_iteration", {
            "invariant": too_strong, "guard": parse_expr("N >= (x+e)*(x+e)"),
            "variant": parse_expr("N - x*x")})
    message = str(caught.value)
    assert "Weaken I" in message and "typically strengthen" not in message


def test_the_exit_check_asks_for_a_stronger_invariant():
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "initialised_iteration", {
            "invariant": parse_expr("x*x <= N"), "guard": parse_expr("e < 0"),
            "variant": parse_expr("N - x*x")})
    assert "strengthen I" in str(caught.value)


def test_an_assignment_is_told_to_change_its_expression():
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "assignment",
                                 {"variable": "x", "expr": parse_expr("x + e")})
    message = str(caught.value)
    assert "Choose a different expression E" in message
    assert "invariant" not in message.split("Counterexample", 1)[-1]


# --- a formula may only use the specification's own names ---------------------------

def test_an_invented_name_is_found():
    from FormalLLM.refinement.vocabulary import unknown_names
    spec = parse_spec(SQRT)
    assert unknown_names(spec, {"invariant": parse_expr("x*x <= N && V = N - x")}) == ["V"]
    assert unknown_names(spec, {"invariant": parse_expr("x*x <= N && x >= 0"),
                                "guard": parse_expr("N >= (x+e)*(x+e)")}) == []


def test_loop_bookkeeping_names_are_allowed_where_the_specification_has_them():
    from FormalLLM.refinement.vocabulary import unknown_names
    body = body_of({**STRONG})
    assert unknown_names(body, {"intermediate": parse_expr("N - (x + e) * (x + e) < V0")}) == []
    assert unknown_names(parse_spec(SQRT), {"intermediate": parse_expr("x < V0")}) == ["V0"]


def test_bound_variables_are_not_invented_names():
    from FormalLLM.refinement.vocabulary import unknown_names
    spec = parse_spec(SQRT)
    formula = parse_expr("exists (k:int) k * k <= N")
    assert unknown_names(spec, {"invariant": formula}) == []


def test_an_invented_name_is_turned_away_before_the_prover_with_the_names_to_use():
    invented = reply("initialised_iteration", invariant="x * x <= N && V = N - x * x", guard="V > 0", variant="V")
    llm = MockProvider([invented, reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    first = graph.attempts[graph.nodes[graph.root_id].attempts[0]]
    assert first.status == AttemptStatus.REJECTED
    assert "uses the name V, which this specification does not define" in first.counterexample
    assert "frame variable x; constants N, e" in first.counterexample
    assert "does not define" in llm.prompts_received[1]


# --- a test on a variable whose starting value is arbitrary ------------------------------

def test_a_split_on_the_answer_variable_is_refused_at_once():
    """The failing run's first move: `if x*x <= N` at the root, where nothing constrains x on entry."""
    with pytest.raises(VerificationError) as caught:
        RefinementEngine().apply(parse_spec(SQRT), "alternation", {"guard": parse_expr("x * x <= N")})
    message = str(caught.value)
    assert "mentions x" in message and "arbitrary" in message
    assert "Test the names that never change (N, e)" in message


def test_a_split_on_the_inputs_is_fine():
    RefinementEngine().apply(parse_spec(SQRT), "alternation", {"guard": parse_expr("N >= 1")})


def test_a_variable_the_precondition_constrains_may_be_tested():
    """Inside a loop body the invariant talks about x, so a test on x is meaningful."""
    body = body_of({**STRONG, "variant": "N - x*x"})
    RefinementEngine(check_feasibility=False).apply(body, "alternation", {"guard": parse_expr("x >= 1")})


def test_a_variable_whose_earlier_value_the_postcondition_uses_may_be_tested():
    spec = parse_spec("Frame: x:int.\nPrecondition: (n:int) := true.\nPostcondition: (n:int) := x = x0 + 1.")
    RefinementEngine(check_feasibility=False).apply(spec, "alternation", {"guard": parse_expr("x < 0")})


def test_the_refusal_is_recorded_as_a_rejected_attempt_the_model_can_read():
    llm = MockProvider([reply("alternation", guard="x * x <= N"), reply("initialised_iteration", **STRONG)])
    refiner = AutomatedRefiner(RefinementEngine(), llm, max_retries=3, assist=True)
    graph = RefinementGraph(parse_spec(SQRT))
    assert refiner.refine_node(graph, graph.root_id) is True
    first = graph.attempts[graph.nodes[graph.root_id].attempts[0]]
    assert first.status == AttemptStatus.REJECTED and "arbitrary" in first.counterexample
    assert "arbitrary" in llm.prompts_received[1]


def test_the_default_allowance_below_one_step_is_ten_calls():
    assert AutomatedRefiner(RefinementEngine(), MockProvider([])).subtree_budget == 10
