"""Three checks found by reading the v8 HumanEval pilot: proof-only names, already-decided tests, array values."""
import pytest
import z3

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine, VerificationError, decided_guard_message
from FormalLLM.refinement.relevance import proof_only_names
from FormalLLM.verification.z3_backend import _value_text

BODY = parse_spec(r"""Frame: r:int.
Precondition: (n:int) := n > 2 /\ 2 <= r /\ r < n /\ r = V0.
Postcondition: (n:int) := 1 <= r /\ r < V0.""")


def test_a_test_on_a_proof_only_name_is_refused():
    """v8 pilot, largest_divisor: `if r = V0` was proved (the precondition makes it true) and the program then
    stopped with NameError: V0 on every test."""
    assert proof_only_names(parse_expr("r = V0 && x0 > 1")) == ["V0", "x0"]
    with pytest.raises(VerificationError, match="exists only in the proof"):
        RefinementEngine().apply(BODY, "alternation", {"guard": parse_expr("r = V0")})


def test_a_value_computed_from_a_proof_only_name_is_refused():
    with pytest.raises(VerificationError, match="exists only in the proof"):
        RefinementEngine().apply(BODY, "assignment", {"variable": "r", "expr": parse_expr("V0 - 1")})
    RefinementEngine().apply(BODY, "assignment", {"variable": "r", "expr": parse_expr("r - 1")})


SIGNS = parse_spec(r"""Frame: r:int.
Precondition: (a:int)(b:int) := a >= 0 /\ b >= 0.
Postcondition: (a:int)(b:int) := r = a + b.""")


def test_a_test_the_precondition_already_decides_is_refused():
    """v8 pilot, multiply: the else branch was split on its parent's test again and again; each then-branch had a
    contradictory precondition, was closed by skip, and the calls ran out."""
    assert "always true" in decided_guard_message(SIGNS, parse_expr("a >= 0 && b >= 0"))
    assert "always false" in decided_guard_message(SIGNS, parse_expr("a < 0"))
    with pytest.raises(VerificationError, match="already decided"):
        RefinementEngine().apply(SIGNS, "alternation", {"guard": parse_expr("a >= 0")})
    assert decided_guard_message(SIGNS, parse_expr("a > b")) == ""


def test_array_values_are_shown_element_by_element():
    """v8 pilot, max_element: counterexamples read `l = Store(K(Int, 2437), 0, 2438)`."""
    base = z3.K(z3.IntSort(), z3.IntVal(2437))
    assert _value_text(base) == "every element 2437"
    stored = z3.Store(base, z3.IntVal(0), z3.IntVal(2438))
    assert _value_text(stored) == "[0] = 2438, every other element 2437"
    twice = z3.Store(stored, z3.IntVal(0), z3.IntVal(5))
    assert _value_text(twice) == "[0] = 5, every other element 2437"


def test_a_quantified_value_is_refused():
    """v8 pilot, iscube: t := (exists k. k*k*k = a) was proved and the emitted program could not run."""
    cube = parse_spec(r"""Frame: t:bool, k:int.
Precondition: (a:int) := true.
Postcondition: (a:int) := (t = true /\ (exists (k:int) k * k * k = a)) \/ (t = false /\ ~(exists (k:int) k * k * k = a)).""")
    with pytest.raises(VerificationError, match="quantifier"):
        RefinementEngine().apply(cube, "assignment", {"variable": "t", "expr": parse_expr("exists (k:int) k * k * k = a")})


def test_a_frame_variable_with_an_arbitrary_start_gets_a_value_before_the_program_runs():
    """v8 batch, integer division: a proved program began with r := n - q * d and crashed with NameError: q."""
    from FormalLLM.lpl.ast import Assignment, SequentialComposition
    from FormalLLM.lpl.typed_python import python_for
    spec = parse_spec(r"""Frame: q:int, r:int.
Precondition: (n:int)(d:int) := n >= 0 /\ d > 0.
Postcondition: (n:int)(d:int) := q * d + r = n /\ r >= 0 /\ r < d.""")
    program = SequentialComposition(Assignment("r", parse_expr("n - q * d")), Assignment("q", parse_expr("0")))
    code = python_for(program, spec)
    assert code.splitlines()[:2] == ["q = 0", "r = 0"]
    env = {"n": 7, "d": 2}
    exec(code, {}, env)                                # no NameError
    pinned = parse_spec(r"""Frame: i:int.
Precondition: (N:int) := i = 0 /\ N >= 0.
Postcondition: (N:int) := i = N.""")
    assert not python_for(Assignment("i", parse_expr("N")), pinned).startswith("i = 0")   # the caller's value is kept
