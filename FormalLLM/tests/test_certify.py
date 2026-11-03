"""A finished derivation can be re-checked end to end by the proof assistants."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.refinement.graph.graph import RefinementGraph
from FormalLLM.tests.test_engine_reachability import apply_step, expr_params
from FormalLLM.verification.backends.coq_backend import CoqBackend
from FormalLLM.verification.backends.lean_backend import LeanBackend
from FormalLLM.verification.certify import (
    certify_derivation, derivation_obligations, render_report,
)

SQRT = (
    "Frame: x.\n"
    "Precondition: (N:float)(e:float) := N >= 0 /\\ e > 0.\n"
    "Postcondition: (N:float)(e:float) := x*x <= N /\\ N < (x+e)*(x+e)."
)

coq = CoqBackend()
lean = LeanBackend()


def sqrt_graph():
    engine, graph = RefinementEngine(), RefinementGraph(parse_spec(SQRT))
    roles = apply_step(graph, engine, graph.root_id, "initialised_iteration", expr_params(
        invariant="(x * x) <= N && x >= 0", guard="N >= (x + e) * (x + e)", variant="N - (x * x)"))
    apply_step(graph, engine, roles["init"], "assignment", {"variable": "x", "expr": parse_expr("0")})
    apply_step(graph, engine, roles["body"], "assignment", {"variable": "x", "expr": parse_expr("x + e")})
    assert graph.is_complete(graph.root_id)
    return engine, graph


def test_the_derivations_obligations_are_recovered():
    engine, graph = sqrt_graph()
    items = derivation_obligations(graph, engine)
    assert [i["law"] for i in items] == ["initialised_iteration", "assignment", "assignment"]
    assert [i["node"] for i in items] == ["N0", "N1", "N2"]


def test_a_step_that_was_rejected_is_not_part_of_the_derivation():
    engine, graph = RefinementEngine(), RefinementGraph(parse_spec(SQRT))
    graph.record_attempt(graph.root_id, "assignment", {"variable": "x", "expr": parse_expr("N")})
    assert derivation_obligations(graph, engine) == []


@pytest.mark.skipif(not coq.available, reason="coqc is not installed")
def test_coq_certifies_the_whole_sqrt_derivation():
    engine, graph = sqrt_graph()
    report = certify_derivation(graph, engine, {"coq": coq})
    assert report["obligations"] == 3
    assert report["coq"]["certified"] == 3, render_report(report)


@pytest.mark.skipif(not lean.available, reason="Lean + Mathlib are not installed")
def test_lean_certifies_the_whole_sqrt_derivation():
    engine, graph = sqrt_graph()
    report = certify_derivation(graph, engine, {"lean": lean})
    assert report["lean"]["certified"] == 3, render_report(report)
