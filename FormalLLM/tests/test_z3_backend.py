import pytest
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.frame import obligation_params
from FormalLLM.verification.z3_backend import verify_obligation
from FormalLLM.verification.proof_obligations import ProofObligation

def test_obligation_params_includes_frame_types():
    """
    Frame variables must be included in obligation_params with their correct types
    so Z3 doesn't default them to Real. This prevents integer quotient bugs (like -9/8).
    """
    spec = parse_spec("Frame: q:int, r:int.\nPrecondition: (n:int) := n >= 0.\nPostcondition: (n:int) := true.")
    params = obligation_params(spec)
    
    names = [p.name for p in params]
    assert "q" in names
    assert "r" in names
    
    q_param = next(p for p in params if p.name == "q")
    assert type(q_param.type_).__name__ == "IntType", "Frame variable 'q' lost its integer type"


def _obl(src_pre, src_post):
    from FormalLLM.lspec.parser import parse_spec
    spec = parse_spec(f"Precondition: (x:int) := {src_pre}.\nPostcondition: (x:int) := {src_post}.")
    return ProofObligation([spec.precondition.expr], spec.postcondition.expr, params=spec.precondition.params)


def test_valid_obligation_is_proved():
    status, _ = verify_obligation(_obl("x > 0", "x >= 0"))
    assert status == "PROVED"


def test_invalid_obligation_fails_with_counterexample():
    status, msg = verify_obligation(_obl("x >= 0", "x > 0"))
    assert status == "FAILED" and "x = 0" in msg


def test_unsupported_operator_is_reported_not_silent():
    from FormalLLM.lspec.ast import BinaryOp, Number
    bad = ProofObligation([], BinaryOp(Number("1"), "^^", Number("2")))
    status, msg = verify_obligation(bad)
    assert status == "UNKNOWN" and "Unsupported binary operator" in msg


def test_timeout_yields_unknown_not_hang():
    # Nonlinear integer arithmetic that Z3 cannot settle quickly.
    from FormalLLM.lspec.parser import parse_spec
    spec = parse_spec(r"Precondition: (x:int)(y:int)(z:int) := x > 2 /\ y > 2 /\ z > 2.""\n"
                      r"Postcondition: (x:int)(y:int)(z:int) := x*x*x + y*y*y <> z*z*z.")
    ob = ProofObligation([spec.precondition.expr], spec.postcondition.expr, params=spec.precondition.params)
    status, _ = verify_obligation(ob, timeout_ms=200)
    assert status in ("UNKNOWN", "PROVED")


def test_unknown_is_a_distinct_error_type():
    from FormalLLM.refinement.engine import VerificationError, VerificationUnknown
    assert issubclass(VerificationUnknown, VerificationError)
