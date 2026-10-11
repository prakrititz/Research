"""The specification evaluator: formulas on concrete values, with the prover's semantics."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.evaluator import EvaluationError, Undefined, check_specification, evaluate
from FormalLLM.lspec.parser import parse_spec


def ev(text, **env):
    return evaluate(parse_expr(text), env)


def test_arithmetic_and_comparison():
    assert ev("a * b + 1", a=3, b=4) == 13
    assert ev("a * a <= n", a=3, n=9) is True
    assert ev("a <> b", a=1, b=2) is True


def test_division_is_whole_for_integers_and_exact_otherwise():
    assert ev("a / b", a=7, b=2) == 3
    assert ev("a / b", a=7.0, b=2) == 3.5
    assert ev("a / b", a=-7, b=2) == -4, "floor division, as the prover's integer division"


def test_division_by_zero_is_undefined_not_an_answer():
    with pytest.raises(Undefined):
        ev("a / b", a=1, b=0)


def test_array_reads_and_slices():
    assert ev("a[1] + a[2]", a=[5, 6, 7]) == 13
    assert ev("a[0:2] = b", a=[5, 6, 7], b=[5, 6]) is True
    with pytest.raises(Undefined):
        ev("a[3]", a=[5, 6, 7])
    with pytest.raises(Undefined):
        ev("a[k]", a=[5, 6, 7], k=-1)


def test_guards_short_circuit_so_reads_can_be_protected():
    assert ev("i >= n \\/ a[i] > 0", a=[1, 2], i=5, n=2) is True
    assert ev("i < n /\\ a[i] > 0", a=[1, 2], i=5, n=2) is False


def test_quantifiers_over_integers():
    assert ev("exists (k:int) n = 2 * k", n=10) is True
    assert ev("exists (k:int) n = 2 * k", n=11) is False
    assert ev("forall (k:int) (k < 0 \\/ k >= len) \\/ a[k] <= m", a=[3, 9, 4], len=3, m=9) is True
    assert ev("forall (k:int) (k < 0 \\/ k >= len) \\/ a[k] <= m", a=[3, 9, 4], len=3, m=8) is False


def test_quantifier_window_grows_with_the_values():
    """A witness as large as twice the input must be found."""
    assert ev("exists (k:int) n = 2 * k", n=3000) is True


def test_real_binders_cannot_be_enumerated():
    with pytest.raises(EvaluationError):
        ev("exists (r:float) r * r = n", n=2)


def test_previous_state_values_come_from_the_environment():
    assert ev("x = x0 + 1", x=5, x0=4) is True
    with pytest.raises(EvaluationError):
        ev("x = x0 + 1", x=5)


def test_a_specification_is_checked_against_a_reference_output():
    spec = parse_spec("Frame: m.\nPrecondition: (n:int) := n >= 0.\nPostcondition: (n:int) := m = n * n.")
    assert check_specification(spec, {"n": 4}, {"m": 16}) is None
    assert "postcondition is false" in check_specification(spec, {"n": 4}, {"m": 15})
    assert "precondition is false" in check_specification(spec, {"n": -1}, {"m": 1})


def test_an_unguarded_read_is_reported_not_hidden():
    spec = parse_spec("Frame: m.\nPrecondition: (a:array int) := true.\nPostcondition: (a:array int) := m = a[0].")
    assert "cannot be evaluated" in check_specification(spec, {"a": []}, {"m": 0})


# --- bounded quantifiers use the bounds their own guards state ---------------------------

def test_a_guarded_forall_checks_only_the_guarded_range():
    """A disjunction of guards is trivially true outside [x, y]; 25,000 values of k must not be tried."""
    import time
    started = time.time()
    formula = r"forall (k:int) k < x \/ k > y \/ k = 2 * (k / 2) \/ k <= r"
    assert ev(formula, x=12, y=12354, r=100) is False        # k = 101 is odd and above r
    assert ev(formula, x=12, y=12354, r=12353) is True
    assert time.time() - started < 1.0


def test_a_guarded_exists_checks_only_the_guarded_range():
    formula = r"exists (k:int) 0 <= k /\ k < n /\ a[k] = m"
    assert ev(formula, a=[4, 8, 15], n=3, m=15) is True
    assert ev(formula, a=[4, 8, 15], n=2, m=15) is False


def test_guard_bounds_agree_with_unbounded_enumeration():
    """The optimisation must not change any answer: compare with the same formula hidden from it."""
    for n in range(0, 12):
        guarded = ev(r"exists (k:int) 0 <= k /\ k <= n /\ k * k = n", n=n)
        hidden = ev(r"exists (k:int) (k * k = n) /\ (0 <= k) /\ (k <= n + 0 * k)", n=n)
        assert guarded == hidden == (int(n ** 0.5) ** 2 == n)


def test_the_earlier_value_of_a_float_variable_is_a_float_too():
    """Found in review: x0 kept its int value, so x0 / 2 became whole-number division."""
    from FormalLLM.lspec.evaluator import check_specification
    from FormalLLM.lspec.parser import parse_spec
    spec = parse_spec("Frame: x:float.\nPrecondition: := true.\nPostcondition: := x = x0 / 2.")
    assert check_specification(spec, {}, {"x": 2.5}, previous={"x0": 5}) is None
