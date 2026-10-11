"""The program that runs must be the program that was proved: integer division stays whole-number."""
import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lpl.ast import Assignment, IfElse, SequentialComposition, While
from FormalLLM.lpl.to_python import to_python
from FormalLLM.lpl.typed_python import declared_kinds, python_for
from FormalLLM.lspec.parser import parse_spec

EVEN = ("Frame: t:bool.\nPrecondition: (n:int) := true.\n"
        "Postcondition: (n:int) := (t = true /\\ n = 2 * (n / 2)) \\/ (t = false /\\ ~(n = 2 * (n / 2))).")
REAL = "Frame: h:float.\nPrecondition: (a:float) := true.\nPostcondition: (a:float) := 2 * h = a."


def run(code, **inputs):
    namespace = dict(inputs)
    exec(code, {}, namespace)
    return namespace


def test_integer_division_is_whole_number_in_the_emitted_code():
    spec = parse_spec(EVEN)
    program = Assignment("t", parse_expr("n = 2 * (n / 2)"))
    code = python_for(program, spec)
    assert "//" in code
    assert [run(code, n=n)["t"] for n in (6, 7, 8, 9)] == [True, False, True, False]


def test_the_untyped_emitter_would_have_been_wrong():
    """The reason this module exists: with `/`, every n looks even."""
    spec = parse_spec(EVEN)
    program = Assignment("t", parse_expr("n = 2 * (n / 2)"))
    assert run(to_python(program), n=9)["t"] is True            # wrong: 9 is odd
    assert run(python_for(program, spec), n=9)["t"] is False


def test_real_division_stays_exact():
    spec = parse_spec(REAL)
    code = python_for(Assignment("h", parse_expr("a / 2")), spec)
    assert "//" not in code and run(code, a=5.0)["h"] == 2.5


def test_an_integer_over_a_real_is_exact():
    spec = parse_spec("Frame: h:float.\nPrecondition: (a:float)(k:int) := true.\nPostcondition: (a:float)(k:int) := true.")
    assert "//" not in python_for(Assignment("h", parse_expr("k / a")), spec)


def test_array_elements_use_their_element_type():
    spec = parse_spec("Frame: m:int.\nPrecondition: (l:array int) := true.\nPostcondition: (l:array int) := true.")
    assert declared_kinds(spec)["l"] == "Z"
    assert "//" in python_for(Assignment("m", parse_expr("l[0] / 2")), spec)


def test_statements_keep_their_structure():
    spec = parse_spec("Frame: r:int, i:int.\nPrecondition: (n:int) := true.\nPostcondition: (n:int) := true.")
    program = SequentialComposition(
        Assignment("i", parse_expr("0")),
        While(parse_expr("i < n"), IfElse(parse_expr("i = 2 * (i / 2)"), Assignment("i", parse_expr("i + 1")),
                                          Assignment("i", parse_expr("i + 2")))))
    code = python_for(program, spec)
    assert "while" in code and "if" in code and "else" in code
    assert run(code, n=5)["i"] == 5
