"""The search prover must read the specification language exactly as the certifiers and the program do."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lpl.typed_python import python_for  # noqa: F401  (the emitter uses // for whole numbers)
from FormalLLM.lspec.ast import ArrayType, FloatType, IntType, Param
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.verification.proof_obligations import ProofObligation
from FormalLLM.verification.z3_backend import VerificationResult, verify_obligation


def verdict(goal, assumptions=(), params=()):
    obligation = ProofObligation(assumptions=[parse_expr(a) for a in assumptions], goal=parse_expr(goal),
                                 params=list(params))
    return verify_obligation(obligation)[0]


INTS = [Param("a", IntType()), Param("b", IntType())]


@pytest.mark.parametrize("a,b", [(7, -2), (-7, 2), (-7, -2), (7, 2), (6, -3), (0, -5)])
def test_whole_number_division_rounds_down_like_python_coq_and_lean(a, b):
    """Z3's own div is Euclidean: 7 div -2 = -3, where Python, Coq (Z.div) and Lean (Int.fdiv) give -4."""
    assert verdict(f"a / b = {a // b}", [f"a = {a}", f"b = {b}"], INTS) == VerificationResult.PROVED
    assert verdict(f"a / b = {a // b + 1}", [f"a = {a}", f"b = {b}"], INTS) == VerificationResult.FAILED


def test_division_by_a_positive_constant_is_unchanged():
    assert verdict("a = 2 * (a / 2) || a = 2 * (a / 2) + 1", [], INTS) == VerificationResult.PROVED


def test_a_float_array_holds_reals_not_whole_numbers():
    """Every array used to be Array(Int, Int): a step valid only for whole numbers was accepted for floats."""
    for element, expected in ((IntType(), VerificationResult.PROVED), (FloatType(), VerificationResult.FAILED)):
        params = [Param("x", ArrayType(element))]
        assert verdict("x[0] + 1 <= x[1]", ["x[0] < x[1]"], params) == expected


def test_an_index_may_be_an_arithmetic_term():
    """Loops over arrays compare neighbours; l[k + 1] used to be a syntax error (only l[(k + 1)] parsed)."""
    spec = parse_spec("Frame: t:bool.\nPrecondition: (l:array int)(n:int) := n >= 2.\n"
                      "Postcondition: (l:array int)(n:int) := forall (k:int) k < 0 \/ k + 1 >= n \/ l[k] <= l[k + 1].")
    assert spec.postcondition.expr is not None
    params = [Param("l", ArrayType(IntType()))]
    assert verdict("l[k + 1] - l[k] >= 0", ["l[k] <= l[k + 1]"], params + [Param("k", IntType())]) \
        == VerificationResult.PROVED
