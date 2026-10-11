r"""Python values <-> Lean source, driven by a Lean type written as text (``List (Nat × String)``, ``Option ℚ``...).

The HumanEval data are Python values (ints, floats, strings, lists, tuples, dicts, ``None``). A specification written in Lean has a
Lean type for every parameter and for the result; this module turns a Python value into a Lean literal of that type
(:func:`literal`), into the form ``test.json`` uses for expected values (:func:`expected_json`), and builds *wrong* values close
to a right one (:func:`mutants`) so that a specification can be checked for rejecting them.

Types understood: ``Int Nat ℚ Bool String Char``, ``List T``, ``Array T``, ``Option T`` and products ``A × B × C`` (right nested).
A Python ``float`` is read as the exact rational it denotes (``Fraction(x)``): a Lean specification about numbers reasons in ℚ, and a
tolerance (``|result - exact| ≤ 1/1000000``, EvalPlus' own) says how far the float computation of the canonical solution may stray.
A Python ``bool`` is accepted where a number is expected (``True + True = 2`` in Python; several EvalPlus inputs rely on it).
A ``dict`` is read as the list of its items.
"""
import json
import math
import re
from fractions import Fraction
from typing import Any, List, Tuple, Union

Ty = Union[str, Tuple]          # "Int" | ("List", Ty) | ("Array", Ty) | ("Option", Ty) | ("Prod", [Ty, ...])

_TOKEN = re.compile(r"\(|\)|×|⊕|[^\s()×⊕]+")


def parse_type(text: str) -> Ty:
    tokens = _TOKEN.findall(text)
    position = 0

    def peek():
        return tokens[position] if position < len(tokens) else None

    def take():
        nonlocal position
        position += 1
        return tokens[position - 1]

    def atom():
        token = take()
        if token == "(":
            inner = either()
            if take() != ")":
                raise ValueError(f"unbalanced parentheses in type {text!r}")
            return inner
        return token

    def application():
        head = atom()
        if isinstance(head, str) and head in ("List", "Array", "Option"):
            return (head, atom())
        return head

    def product():
        parts = [application()]
        while peek() == "×":
            take()
            parts.append(application())
        return parts[0] if len(parts) == 1 else ("Prod", parts)

    def either():
        parts = [product()]
        while peek() == "⊕":
            take()
            parts.append(product())
        return parts[0] if len(parts) == 1 else ("Sum", parts)

    result = either()
    if position != len(tokens):
        raise ValueError(f"cannot read type {text!r}")
    return result


def _string(text: str) -> str:
    from FormalLLM.lean.task import lean_string
    return lean_string(text)


def _char(c: str) -> str:
    if len(c) != 1:
        raise ValueError(f"{c!r} is not one character")
    escapes = {"\n": "\\n", "\t": "\\t", "\r": "\\r", "\\": "\\\\", "'": "\\'", '"': '\\"'}
    if c in escapes:
        return f"'{escapes[c]}'"
    if ord(c) < 32 or ord(c) == 127:
        return f"'\\x{ord(c):02x}'"
    return f"'{c}'"


#: How a Python float becomes a rational. ``True``: the number as written (``0.1`` is 1/10), which keeps the numerals small, so that
#: Lean evaluates a specification quickly and a reader recognises the numbers; ``False``: the exact binary value (``0.1`` is
#: 3602879701896397/36028797018963968), which reproduces IEEE comparisons exactly but gives numerals of 50 digits and slow evaluation.
DECIMAL = True


def _rational(value) -> Fraction:
    if isinstance(value, bool):
        return Fraction(int(value))
    if isinstance(value, (int, Fraction)):
        return Fraction(value)
    if isinstance(value, float):
        if math.isnan(value) or math.isinf(value):
            raise ValueError("not a finite number")
        return Fraction(repr(value)) if DECIMAL else Fraction(value)
    raise ValueError(f"{value!r} is not a number")


def _pyval(value: Any) -> str:
    """Any Python value as the constructor term of the ``PyVal`` inductive type (ints, floats, strings, lists, dicts, None)."""
    if value is None:
        return "PyVal.none"
    if isinstance(value, bool):
        return f"(PyVal.bool {'true' if value else 'false'})"
    if isinstance(value, int):
        return f"(PyVal.int ({value}))"
    if isinstance(value, float):
        return f"(PyVal.float {literal(value, 'ℚ')})"
    if isinstance(value, str):
        return f"(PyVal.str {_string(value)})"
    if isinstance(value, (list, tuple)):
        return "(PyVal.list [" + ", ".join(_pyval(v) for v in value) + "])"
    if isinstance(value, dict):
        return "(PyVal.dict [" + ", ".join(f"({_pyval(k)}, {_pyval(v)})" for k, v in value.items()) + "])"
    raise ValueError(f"no PyVal for {value!r}")


def literal(value: Any, ty: Union[str, Ty]) -> str:
    """Lean source of ``value`` at type ``ty`` (not parenthesised; wrap it when it is an argument)."""
    ty = parse_type(ty) if isinstance(ty, str) else ty
    if ty in ("Int", "Nat"):
        if isinstance(value, float) or not isinstance(value, (int, bool)):
            raise ValueError(f"{value!r} is not an {ty}")
        number = int(value)
        if ty == "Nat" and number < 0:
            raise ValueError("negative Nat")
        return str(number)
    if ty == "ℚ":
        q = _rational(value)
        return f"({q.numerator} : ℚ)" if q.denominator == 1 else f"({q.numerator} / {q.denominator} : ℚ)"
    if ty == "PyVal":
        return _pyval(value)
    if ty == "Bool":
        if not isinstance(value, bool):
            raise ValueError(f"{value!r} is not a Bool")
        return "true" if value else "false"
    if ty == "String":
        if not isinstance(value, str):
            raise ValueError(f"{value!r} is not a String")
        return _string(value)
    if ty == "Char":
        if not isinstance(value, str):
            raise ValueError(f"{value!r} is not a Char")
        return _char(value)
    if isinstance(ty, tuple) and ty[0] in ("List", "Array"):
        if isinstance(value, dict):
            value = list(value.items())
        if not isinstance(value, (list, tuple)):
            raise ValueError(f"{value!r} is not a {ty[0]}")
        body = ", ".join(literal(v, ty[1]) for v in value)
        return f"[{body}]" if ty[0] == "List" else f"#[{body}]"
    if isinstance(ty, tuple) and ty[0] == "Option":
        return "none" if value is None else f"some ({literal(value, ty[1])})"
    if isinstance(ty, tuple) and ty[0] == "Prod":
        if not isinstance(value, (list, tuple)) or len(value) != len(ty[1]):
            raise ValueError(f"{value!r} does not fit {len(ty[1])} components")
        return "(" + ", ".join(literal(v, t) for v, t in zip(value, ty[1])) + ")"
    if isinstance(ty, tuple) and ty[0] == "Sum":
        left, right = ty[1][0], (ty[1][1] if len(ty[1]) == 2 else ("Sum", ty[1][1:]))
        try:
            return f"Sum.inl ({literal(value, left)})"
        except (ValueError, TypeError):
            return f"Sum.inr ({literal(value, right)})"
    raise ValueError(f"no literal for type {ty}")


def lean_literal(value: Any, type_text: str) -> str:
    return literal(value, type_text)


def expected_json(value: Any, type_text: str):
    """The ``test.json`` convention: numbers, booleans and strings are JSON values; other types are Lean literals."""
    ty = parse_type(type_text)
    if ty in ("Int", "Nat"):
        return int(value) if isinstance(value, bool) else value
    if ty in ("Bool", "String"):
        return value
    return literal(value, ty)


def _other(ty: Ty):
    """Some value of the type, used when a list has to grow."""
    if ty in ("Int", "Nat"):
        return 7
    if ty == "ℚ":
        return 7
    if ty == "Bool":
        return True
    if ty == "String":
        return "z"
    if ty == "Char":
        return "z"
    if isinstance(ty, tuple) and ty[0] in ("List", "Array"):
        return [_other(ty[1])]
    if isinstance(ty, tuple) and ty[0] == "Option":
        return _other(ty[1])
    if isinstance(ty, tuple) and ty[0] == "Prod":
        return tuple(_other(t) for t in ty[1])
    if isinstance(ty, tuple) and ty[0] == "Sum":
        return _other(ty[1][0])
    return 7


def _same(a, b) -> bool:
    try:
        return a == b
    except Exception:
        return False


def mutants(value: Any, type_text: Union[str, Ty], limit: int = 3) -> List[Any]:
    """Wrong answers close to ``value`` (Python values at the same type): a specification has to reject them."""
    ty = parse_type(type_text) if isinstance(type_text, str) else type_text
    out: List[Any] = []
    if ty == "Bool":
        out = [not value]
    elif ty in ("Int", "Nat"):
        v = int(value)
        out = [v + 1, v - 1, v * 2 + 3] if ty == "Int" else [v + 1] + ([v - 1] if v > 0 else []) + [v * 2 + 3]
    elif ty == "ℚ":
        v = _rational(value)
        out = [v + 1, v - 1, v * 2 + 3]
    elif ty == "PyVal":
        if value is None:
            out = [7]
        elif isinstance(value, bool):
            out = [not value]
        elif isinstance(value, (int, float)):
            out = [value + 1, value - 1]
        elif isinstance(value, str):
            out = [value + "x", value[:-1] if value else "a"]
        elif isinstance(value, (list, tuple)):
            out = [list(value)[:-1] if value else [7], list(value) + [7]]
    elif ty == "Char":
        out = [chr(ord(value) + 1), "z" if value != "z" else "a"]
    elif ty == "String":
        out = [value + "x", value[:-1] if value else "a", value[::-1] if value[::-1] != value else value + "yy"]
        if value:
            out.append(chr(ord(value[0]) + 1) + value[1:])
    elif isinstance(ty, tuple) and ty[0] in ("List", "Array"):
        elem = ty[1]
        items = list(value.items()) if isinstance(value, dict) else list(value)
        out = [items[:-1] if items else [_other(elem)], items + [_other(elem)],
               items[::-1] if items[::-1] != items else items + items + [_other(elem)]]
        if items:
            changed = mutants(items[0], elem, 1)
            if changed:
                out.append([changed[0]] + items[1:])
    elif isinstance(ty, tuple) and ty[0] == "Option":
        out = [_other(ty[1])] if value is None else [None, *mutants(value, ty[1], 1)]
    elif isinstance(ty, tuple) and ty[0] == "Sum":
        for side in ty[1]:
            try:
                literal(value, side)
            except (ValueError, TypeError):
                continue
            out = mutants(value, side, limit)
            break
    elif isinstance(ty, tuple) and ty[0] == "Prod":
        parts = list(value)
        for k, t in enumerate(ty[1]):
            changed = mutants(parts[k], t, 1)
            if changed:
                out.append(tuple(parts[:k] + [changed[0]] + parts[k + 1:]))
    unique: List[Any] = []
    for candidate in out:
        if _same(candidate, value) or any(_same(candidate, u) for u in unique):
            continue
        unique.append(candidate)
    return unique[:limit]
