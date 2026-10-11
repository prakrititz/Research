"""Lean 4 translation and certification of proof obligations.

Translation tests need no toolchain. Tests that run Lean are skipped when it is
not installed; each takes several seconds because Mathlib is imported per run.
"""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.coq_translator import UnsupportedForBackend
from FormalLLM.lspec.lean_translator import obligation_to_lean
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.frame import obligation_params
from FormalLLM.verification.backends import get_backend
from FormalLLM.verification.backends.lean_backend import LeanBackend
from FormalLLM.verification.proof_obligations import ProofObligation

lean = LeanBackend()
needs_lean = pytest.mark.skipif(not lean.available, reason="Lean + Mathlib are not installed")


def obligation(pre, post, decls="(N:float)(e:float)(x:float)"):
    spec = parse_spec(f"Precondition: {decls} := true.\nPostcondition: {decls} := true.")
    return ProofObligation([parse_expr(pre)], parse_expr(post), params=obligation_params(spec))


# --- translation -------------------------------------------------------------

def test_real_obligation_is_printed_with_real_binders_and_hypotheses():
    header, sorts, parts = obligation_to_lean(obligation("x >= 0 && x * x <= N", "x <= N + 1 && x >= 0"))
    assert sorts == {"N": "R", "x": "R"}
    assert "(N x : ℝ)" in header
    assert "(h0 : (x ≥ (0 : ℝ)))" in header and "(h1 :" in header
    assert parts == 2


def test_integer_obligation_uses_integers_and_floor_division():
    header, sorts, _ = obligation_to_lean(obligation("n >= 0 && d > 0", "n / d >= 0", "(n:int)(d:int)"))
    assert sorts == {"n": "Z", "d": "Z"}
    assert "(d n : ℤ)" in header and "Int.fdiv" in header


def test_integers_used_as_reals_are_cast_at_the_leaves():
    header, _, _ = obligation_to_lean(obligation("i >= 0", "i * r >= 0", "(i:int)(r:float)"))
    assert "(↑i : ℝ)" in header


def test_nat_variables_get_a_non_negativity_hypothesis():
    header, _, _ = obligation_to_lean(obligation("true", "n >= 0", "(n:nat)"))
    assert "(0 ≤ n)" in header


def test_unsupported_constructs_are_reported_not_dropped():
    with pytest.raises(UnsupportedForBackend):
        obligation_to_lean(obligation("true", "a[1:2] = 0", "(a:array int)"))


def test_backend_selection_knows_lean():
    assert get_backend("lean").name == "lean"
    assert get_backend("cross-lean").name == "cross-lean"


# --- certification (needs Lean) ----------------------------------------------

@needs_lean
def test_the_paper_sqrt_loop_body_obligation_is_certified():
    pre = ("N >= 0 && e > 0 && x * x <= N && x >= 0 && N >= (x + e) * (x + e) && N - x * x = V0")
    post = ("N >= 0 && e > 0 && (x + e) * (x + e) <= N && x + e >= 0 && "
            "0 <= N - (x + e) * (x + e) && N - (x + e) * (x + e) < V0")
    status, message = lean.verify(obligation(pre, post, "(N:float)(e:float)(x:float)(V0:float)"))
    assert status == "PROVED", message


@needs_lean
def test_integer_arithmetic_is_certified():
    status, message = lean.verify(obligation("q * d + r = n && r >= d", "(q + 1) * d + (r - d) = n",
                                             "(q:int)(d:int)(r:int)(n:int)"))
    assert status == "PROVED", message


@needs_lean
def test_a_false_obligation_is_unknown_never_proved_and_never_failed():
    status, _ = lean.verify(obligation("x >= 0", "x > 0"))
    assert status == "UNKNOWN"
