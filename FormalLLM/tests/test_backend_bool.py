"""Boolean-valued results in Coq and Lean: a bool variable is a proposition.

`t = true` is `t`, `t = false` is `~ t`, and an assignment `t := C` substitutes the proposition `C`
for `t`, which is what the obligation means. Needed by the HumanEval problems whose result is a
truth value (HumanEval/157, /138, ...).
"""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.coq_translator import UnsupportedForBackend, obligation_to_coq
from FormalLLM.lspec.lean_translator import obligation_to_lean
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.verification.backends.coq_backend import CoqBackend
from FormalLLM.verification.backends.lean_backend import LeanBackend

PARITY = (r"Frame: t:bool." "\n"
          r"Precondition: (n:int) := true." "\n"
          r"Postcondition: (n:int) := (t = true /\ (n >= 8 /\ n = 2 * (n / 2))) \/ "
          r"(t = false /\ ~(n >= 8 /\ n = 2 * (n / 2)))." "\n")

coq, lean = CoqBackend(), LeanBackend()


def parity_obligation():
    result = RefinementEngine().apply(parse_spec(PARITY), "assignment",
                                      {"variable": "t", "expr": parse_expr("n >= 8 && n = 2 * (n / 2)")})
    return result.obligations[0]


def test_a_boolean_variable_is_a_proposition_in_coq():
    spec = parse_spec(PARITY)
    from FormalLLM.verification.proof_obligations import ProofObligation
    from FormalLLM.refinement.frame import obligation_params
    obligation = ProofObligation([parse_expr("n >= 0")], spec.postcondition.expr,
                                 params=obligation_params(spec))
    text, sorts = obligation_to_coq(obligation)
    assert sorts["t"] == "P" and "(t : Prop)" in text
    assert "(t <-> True)" in text and "(t <-> False)" in text


def test_the_assignment_obligation_has_no_free_boolean_left():
    text, sorts = obligation_to_coq(parity_obligation())
    assert "P" not in sorts.values(), "t was substituted away"
    assert "<->" in text


def test_a_boolean_where_a_number_is_needed_is_refused_not_guessed():
    from FormalLLM.verification.proof_obligations import ProofObligation
    from FormalLLM.refinement.frame import obligation_params
    spec = parse_spec(PARITY)
    obligation = ProofObligation([parse_expr("true")], parse_expr("t + 1 > 0"), params=obligation_params(spec))
    with pytest.raises(UnsupportedForBackend):
        obligation_to_coq(obligation)


def test_lean_prints_the_same_obligation_with_iff():
    header, sorts, _ = obligation_to_lean(parity_obligation())
    assert "↔" in header


@pytest.mark.skipif(not coq.available, reason="coqc is not installed")
def test_coq_certifies_the_boolean_assignment():
    assert coq.verify(parity_obligation())[0] == "PROVED"


@pytest.mark.skipif(not lean.available, reason="Lean is not installed")
def test_lean_certifies_the_boolean_assignment():
    assert lean.verify(parity_obligation())[0] == "PROVED"


@pytest.mark.skipif(not coq.available, reason="coqc is not installed")
def test_a_wrong_boolean_assignment_is_not_certified():
    wrong = RefinementEngine(check_feasibility=False)
    # n >= 8 alone is not the specification: odd n >= 9 would come out true. Z3 refuses it first.
    from FormalLLM.refinement.engine import VerificationError
    with pytest.raises(VerificationError):
        wrong.apply(parse_spec(PARITY), "assignment", {"variable": "t", "expr": parse_expr("n >= 8")})
