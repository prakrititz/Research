"""Z3 first; Lean only for what Z3 leaves unknown -- and only a proof is taken from it."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError, VerificationUnknown
from FormalLLM.verification.backends import get_backend
from FormalLLM.verification.backends.base import VerificationResult
from FormalLLM.verification.backends.fallback import FallbackBackend
from FormalLLM.verification.backends.lean_backend import LeanBackend
from FormalLLM.verification.proof_obligations import ProofObligation

needs_lean = pytest.mark.skipif(not LeanBackend().available, reason="Lean + Mathlib are not installed")


class Scripted:
    """A stand-in prover that answers from a list and records how often it was asked."""
    name = "scripted"

    def __init__(self, *answers):
        self.answers, self.asked = list(answers), 0

    def verify(self, obligation, timeout_ms=None):
        self.asked += 1
        return self.answers.pop(0)


def backend(z3_answer, prover_answer):
    chosen = FallbackBackend.__new__(FallbackBackend)
    chosen.name, chosen.z3, chosen.prover = "z3+scripted", Scripted(z3_answer), Scripted(prover_answer)
    chosen.rescued = chosen.still_unknown = 0
    return chosen


OB = ProofObligation([parse_expr("x > 0")], parse_expr("x >= 0"))


def test_what_z3_proves_is_not_sent_to_the_prover():
    b = backend((VerificationResult.PROVED, "valid"), (VerificationResult.PROVED, "never asked"))
    assert b.verify(OB)[0] == VerificationResult.PROVED and b.prover.asked == 0


def test_what_z3_refutes_keeps_its_counterexample_and_is_not_second_guessed():
    b = backend((VerificationResult.FAILED, "Counterexample: x = 1"), (VerificationResult.PROVED, "never asked"))
    status, message = b.verify(OB)
    assert status == VerificationResult.FAILED and "x = 1" in message and b.prover.asked == 0


def test_what_z3_cannot_decide_is_accepted_only_on_a_proof():
    b = backend((VerificationResult.UNKNOWN, "timeout"), (VerificationResult.PROVED, "Certified by Lean."))
    status, message = b.verify(OB)
    assert status == VerificationResult.PROVED and "could not decide" in message and b.rescued == 1


def test_a_prover_that_finds_nothing_leaves_the_answer_unknown_not_failed():
    b = backend((VerificationResult.UNKNOWN, "timeout"), (VerificationResult.UNKNOWN, "tactics did not close it"))
    status, message = b.verify(OB)
    assert status == VerificationResult.UNKNOWN and "timeout" in message and b.still_unknown == 1


def test_the_backend_is_selectable_by_name():
    assert get_backend("z3+lean").name == "z3+lean" and get_backend("z3+coq").name == "z3+coq"


@needs_lean
def test_a_quantified_step_z3_gives_up_on_is_proved_by_lean_and_accepted_by_the_engine(monkeypatch):
    """HumanEval/102 (choose_num) has quantified, parity-based steps. Z3 normally decides them, so it
    is told to give up here (as it does on harder quantified goals); the real Lean then proves the
    step, and the engine accepts it."""
    from benchmarks.datasets.he_specs import SPECS
    chosen = get_backend("z3+lean")
    monkeypatch.setattr(chosen.z3, "verify", lambda obligation, timeout_ms=None:
                        (VerificationResult.UNKNOWN, "Solver returned unknown: forced for the test"))
    engine = RefinementEngine(backend=chosen, check_feasibility=False)
    spec = parse_spec(SPECS["HumanEval/102"]["spec"])
    # the branch x > y: r := -1 satisfies the first disjunct of the postcondition
    branch = engine.apply(spec, "alternation", {"guard": parse_expr("x > y")}).by_role()["then"]
    engine.apply(branch, "assignment", {"variable": "r", "expr": parse_expr("0 - 1")})
    assert chosen.rescued == 1


@needs_lean
def test_a_wrong_step_is_not_rescued(monkeypatch):
    from benchmarks.datasets.he_specs import SPECS
    chosen = get_backend("z3+lean")
    monkeypatch.setattr(chosen.z3, "verify", lambda obligation, timeout_ms=None:
                        (VerificationResult.UNKNOWN, "Solver returned unknown: forced for the test"))
    engine = RefinementEngine(backend=chosen, check_feasibility=False)
    spec = parse_spec(SPECS["HumanEval/102"]["spec"])
    branch = engine.apply(spec, "alternation", {"guard": parse_expr("x > y")}).by_role()["then"]
    with pytest.raises(VerificationUnknown):
        engine.apply(branch, "assignment", {"variable": "r", "expr": parse_expr("y")})   # y is not -1
    assert chosen.rescued == 0 and chosen.still_unknown == 1
