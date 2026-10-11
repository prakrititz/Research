"""A guard is a test the finished program must run, so it may not contain a quantifier."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError
from FormalLLM.refinement.relevance import has_quantifier, unexecutable_guard_message

SPEC = r"""Frame: t:bool.
Precondition: (n:int) := n >= 2.
Postcondition: (n:int) := (t = true /\ ~(exists (k:int) 2 <= k /\ k < n /\ n = k * (n / k))) \/ (t = false /\ (exists (k:int) 2 <= k /\ k < n /\ n = k * (n / k)))."""


def test_quantified_guards_are_detected():
    assert has_quantifier(parse_expr("exists (k:int) 0 <= k && k < n && l[k] >= t"))
    assert not has_quantifier(parse_expr("n >= 2 && l[0] > 1"))
    assert unexecutable_guard_message(parse_expr("n >= 2")) == ""
    assert "quantifier" in unexecutable_guard_message(parse_expr("exists (k:int) k < n && k > 0"))


@pytest.mark.parametrize("law,params", [
    ("alternation", {"guard": "exists (k:int) 2 <= k && k < n && n = k * (n / k)"}),
])
def test_the_engine_refuses_a_quantified_guard(law, params):
    engine = RefinementEngine()
    with pytest.raises(VerificationError, match="quantifier"):
        engine.apply(parse_spec(SPEC), law, {k: parse_expr(v) for k, v in params.items()})


def test_a_plain_guard_is_still_accepted():
    engine = RefinementEngine()
    engine.apply(parse_spec(SPEC), "alternation", {"guard": parse_expr("n = 2")})
