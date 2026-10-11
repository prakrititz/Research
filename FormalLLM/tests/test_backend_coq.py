"""Coq/Rocq translation and certification of proof obligations.

Translation tests need no toolchain. Tests that run ``coqc`` are skipped when it
is not installed (see FormalLLM/verification/backends/coq_backend.py).
"""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.coq_translator import UnsupportedForBackend, obligation_to_coq
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.frame import obligation_params
from FormalLLM.verification.backends import get_backend
from FormalLLM.verification.backends.coq_backend import CoqBackend
from FormalLLM.verification.proof_obligations import ProofObligation

coq = CoqBackend()
needs_coq = pytest.mark.skipif(not coq.available, reason="coqc is not installed")


def obligation(pre, post, decls="(N:float)(e:float)(x:float)"):
    """Build an obligation from model-facing syntax (&&, ||, !) and declared sorts."""
    spec = parse_spec(f"Precondition: {decls} := true.\nPostcondition: {decls} := true.")
    return ProofObligation([parse_expr(pre)], parse_expr(post), params=obligation_params(spec))


# --- translation -------------------------------------------------------------

def test_real_obligation_is_printed_with_real_binders_and_scopes():
    text, sorts = obligation_to_coq(obligation("x >= 0 && x * x <= N", "x <= N + 1"))
    assert sorts == {"N": "R", "x": "R"}
    assert "forall (N x : R)" in text
    assert "%R" in text and "%Z" not in text


def test_integer_obligation_uses_z_and_integer_division():
    text, sorts = obligation_to_coq(obligation("n >= 0 && d > 0", "n / d >= 0", "(n:int)(d:int)"))
    assert sorts == {"n": "Z", "d": "Z"}
    assert "Z.div" in text


def test_mixed_integer_and_real_terms_are_cast_with_izr():
    text, _ = obligation_to_coq(obligation("i >= 0", "i * r >= 0", "(i:int)(r:float)"))
    assert "IZR" in text


def test_nat_variables_get_a_non_negativity_hypothesis():
    """Coq's nat is non-negative; the Z3 translator's is not (documented difference)."""
    text, _ = obligation_to_coq(obligation("true", "n >= 0", "(n:nat)"))
    assert "(0 <= n)%Z" in text


def test_previous_state_name_gets_the_sort_of_its_variable():
    spec = parse_spec("Frame: x:int.\nPrecondition: (n:int) := x0 < n.\nPostcondition: (n:int) := x0 < n.")
    text, sorts = obligation_to_coq(ProofObligation([spec.precondition.expr], spec.postcondition.expr,
                                                    params=obligation_params(spec)))
    assert sorts.get("x0") == "Z"


def test_unsupported_constructs_are_reported_not_dropped():
    with pytest.raises(UnsupportedForBackend):
        obligation_to_coq(obligation("true", "a[1:2] = 0", "(a:array int)"))


def test_backend_selection():
    assert get_backend("z3").name == "z3"
    assert get_backend("coq").name == "coq"
    with pytest.raises(ValueError):
        get_backend("isabelle")


# --- certification (needs coqc) ----------------------------------------------

@needs_coq
def test_a_true_real_obligation_is_certified():
    status, message = coq.verify(obligation("x >= 0 && x * x <= N", "x * x <= N + 1"))
    assert status == "PROVED", message
    assert "Certified" in message


@needs_coq
def test_a_false_obligation_is_unknown_never_proved_and_never_failed():
    status, _ = coq.verify(obligation("x >= 0", "x > 0"))
    assert status == "UNKNOWN"          # no counterexample from a proof assistant


@needs_coq
def test_the_paper_sqrt_loop_body_obligation_is_certified():
    pre = ("N >= 0 && e > 0 && x * x <= N && x >= 0 && N >= (x + e) * (x + e) && N - x * x = V0")
    post = ("N >= 0 && e > 0 && (x + e) * (x + e) <= N && x + e >= 0 && "
            "0 <= N - (x + e) * (x + e) && N - (x + e) * (x + e) < V0")
    status, message = coq.verify(obligation(pre, post, "(N:float)(e:float)(x:float)(V0:float)"))
    assert status == "PROVED", message


@needs_coq
def test_integer_arithmetic_is_certified():
    status, message = coq.verify(obligation("q * d + r = n && r >= d", "(q + 1) * d + (r - d) = n",
                                            "(q:int)(d:int)(r:int)(n:int)"))
    assert status == "PROVED", message


@needs_coq
def test_results_are_cached():
    o = obligation("x >= 1", "x >= 0")
    coq.verify(o)
    before = coq.stats["cached"]
    coq.verify(o)
    assert coq.stats["cached"] == before + 1


# --- a numeral does not make a variable whole -------------------------------------

def test_a_name_pinned_only_by_a_numeral_stays_real():
    """`x = 0` is satisfied by a real x. Declaring it Z forced `IZR x * IZR x <= N`, which lra
    cannot connect to `x = 0`; a skip in a square-root derivation then went uncertified."""
    text, sorts = obligation_to_coq(obligation("N >= 0 && x = 0", "x * x <= N"))
    assert sorts["x"] == "R" and "IZR" not in text


def test_a_name_defined_from_an_integer_name_is_still_whole():
    """The case the inference exists for: the variant's start (here D) defined as n - i, n and i integers."""
    _, sorts = obligation_to_coq(obligation("n - i = D", "D >= 0", "(n:int)(i:int)"))
    assert sorts["D"] == "Z"


@needs_coq
def test_the_pinned_variable_obligation_is_certified():
    status, _ = coq.verify(obligation("N >= 0 && e > 0 && x = 0", "x * x <= N && x >= 0"))
    assert status == "PROVED"
