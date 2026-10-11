"""The relaxed termination rule (V < V0) must not accept a loop whose integer measure can decrease for ever."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError

GCD = r"""Frame: g:int, x:int, y:int.
Precondition: (a:int)(b:int) := a > 0 /\ b > 0.
Postcondition: (a:int)(b:int) := g > 0 /\ a = g * (a / g) /\ b = g * (b / g) /\ (forall (d:int) d <= 0 \/ d > a \/ (~(a = d * (a / d) /\ b = d * (b / d))) \/ d <= g)."""
SQRT = r"""Frame: x.
Precondition: (N:float)(e:float) := N >= 0 /\ e > 0.
Postcondition: (N:float)(e:float) := x*x <= N /\ N < (x+e)*(x+e)."""


def loop(spec_text, **params):
    return RefinementEngine().apply(parse_spec(spec_text), "initialised_iteration",
                                    {k: parse_expr(v) for k, v in params.items()})


def test_the_relaxed_rule_refuses_a_measure_that_can_decrease_for_ever(monkeypatch):
    """v8 pilot, gcd: `while g is not a common divisor: g := g + 1` with measure a - g was accepted under the relaxed
    rule; the program never stops when a does not divide b."""
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    with pytest.raises(VerificationError):                      # refused (Z3 may only answer "unknown" here)
        loop(GCD, invariant="g > 0 && (forall (d:int) d <= 0 || d > a || !(a = d * (a / d) && b = d * (b / d)) || d <= g)",
             guard="!(a = g * (a / g) && b = g * (b / g))", variant="a - g")


COUNT = r"""Frame: x:int.
Precondition: (N:int) := N >= 0.
Postcondition: (N:int) := x = N."""


def test_the_new_obligation_has_a_counterexample_for_an_unbounded_measure(monkeypatch):
    """while x != N: x := x + 1 with measure N - x decreases on every iteration, yet never stops if x starts above N."""
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    with pytest.raises(VerificationError, match="measure is never negative"):
        loop(COUNT, invariant="true", guard="x != N", variant="N - x")
    loop(COUNT, invariant="x <= N", guard="x != N", variant="N - x")      # bounded by the invariant: accepted


def test_the_relaxed_rule_still_accepts_the_papers_measure(monkeypatch):
    """N - (x+e)^2 is negative only after the last iteration, when the guard is already false."""
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    loop(SQRT, invariant="x * x <= N && x >= 0", guard="N >= (x + e) * (x + e)", variant="N - (x + e) * (x + e)")


def test_the_strict_rule_is_unchanged(monkeypatch):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "1")
    result = loop(SQRT, invariant="x * x <= N && x >= 0", guard="N >= (x + e) * (x + e)", variant="N - x * x")
    assert len(result.obligations) == 1
