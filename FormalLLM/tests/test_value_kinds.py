"""A number is not a truth value: the engine refuses ill-typed assignments before proving anything."""
import pytest

from FormalLLM.agent.assist import LeafSolver, candidate_expressions
from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError

BOOL = parse_spec("Frame: b:bool.\nPrecondition: (n:int) := n < 0.\n"
                  "Postcondition: (n:int) := (b = true /\ n >= 0) \/ (b = false /\ n < 0).")
NUM = parse_spec("Frame: x:int, y:float.\nPrecondition: (n:int)(f:float) := n > 0.\n"
                 "Postcondition: (n:int)(f:float) := x >= n \/ y = f.")


@pytest.mark.parametrize("expr", ["0", "1", "n", "n + 1"])
def test_a_number_cannot_be_assigned_to_a_truth_value(expr):
    """Measured: b := 0 was proved for a Boolean b (Z3's Python API reads false as 0 when compared)."""
    with pytest.raises(VerificationError, match="truth value"):
        RefinementEngine().apply(BOOL, "assignment", {"variable": "b", "expr": parse_expr(expr)})


def test_true_false_and_tests_are_fine():
    RefinementEngine().apply(BOOL, "assignment", {"variable": "b", "expr": parse_expr("false")})
    RefinementEngine().apply(BOOL, "assignment", {"variable": "b", "expr": parse_expr("n >= 0")})


def test_a_test_cannot_be_assigned_to_a_number_nor_a_real_to_an_int():
    engine = RefinementEngine()
    with pytest.raises(VerificationError, match="is a test"):
        engine.apply(NUM, "assignment", {"variable": "x", "expr": parse_expr("n > 0")})
    with pytest.raises(VerificationError, match="whole number"):
        engine.apply(NUM, "assignment", {"variable": "x", "expr": parse_expr("f")})
    engine.apply(NUM, "assignment", {"variable": "x", "expr": parse_expr("n")})
    engine.apply(NUM, "assignment", {"variable": "y", "expr": parse_expr("f")})


def test_the_assist_offers_truth_values_for_a_boolean_and_array_reads_for_a_number():
    assert candidate_expressions(BOOL, "b")[:2] == ["true", "false"]
    scan = parse_spec("Frame: m:int, i:int.\nPrecondition: (l:array int)(n:int) := n >= 1.\n"
                      "Postcondition: (l:array int)(n:int) := m = l[0].")
    options = candidate_expressions(scan, "m")
    assert "l[0]" in options and "l[i]" in options and "l" not in options
    law, params, _ = LeafSolver(RefinementEngine()).solve(BOOL)
    assert law == "assignment" and str(params["expr"]) != "Number(value='0')"


def test_a_boolean_defined_by_an_equation_gets_that_test_as_a_candidate():
    """Found in review: limiting a Boolean to true/false dropped t := a < b for a postcondition t = (a < b)."""
    spec = parse_spec("Frame: t:bool.\nPrecondition: (a:int)(b:int) := true.\n"
                      "Postcondition: (a:int)(b:int) := t = (a < b).")
    assert "a < b" in candidate_expressions(spec, "t")
    law, params, _ = LeafSolver(RefinementEngine()).solve(spec)
    assert law == "assignment"
