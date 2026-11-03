"""Is the assigned value of the variable's type?

``b := 0`` for a Boolean ``b`` used to be *accepted*: Z3's Python API quietly turns a Boolean into
the integer 0 or 1 when the two are compared, so ``0 = true`` became ``0 = 1`` and the step was
proved. Measured on the HumanEval pilot: a derived ``below_threshold`` set its Boolean answer
with ``b := 1`` and ``b := 0``; it only ran correctly because Python also equates ``1`` with
``True``. A step that puts a number into a truth value (or a truth value into a number, or a real
into an integer) is refused with that explanation, before any proof is attempted.
"""
from typing import Dict, Optional

from FormalLLM.lpl.typed_python import declared_kinds
from FormalLLM.lspec.ast import (
    ArraySelect, BinaryOp, BooleanConst, Const, Number, QuantifiedExpr, UnaryOp, Variable,
    VariablePreviousState,
)

_ARITH = {"+", "-", "*", "/"}
_NAMES = {"B": "a truth value (bool)", "Z": "a whole number (int)", "R": "a number (float)"}


def value_kind(expr, kinds: Dict[str, str]) -> Optional[str]:
    """``"B"``, ``"Z"`` or ``"R"`` for the value of ``expr``, or ``None`` when a name's type is unknown."""
    if isinstance(expr, BooleanConst) or isinstance(expr, QuantifiedExpr):
        return "B"
    if isinstance(expr, Number):
        return "R" if "." in str(expr.value) else "Z"
    if isinstance(expr, (Variable, Const, VariablePreviousState)):
        return kinds.get(expr.name)
    if isinstance(expr, ArraySelect):
        return kinds.get(expr.array)
    if isinstance(expr, UnaryOp):
        return "B" if expr.op == "~" else value_kind(expr.expr, kinds)
    if isinstance(expr, BinaryOp):
        if expr.op not in _ARITH:
            return "B"                                   # a comparison or a connective
        left, right = value_kind(expr.left, kinds), value_kind(expr.right, kinds)
        if left is None or right is None:
            return None
        if "B" in (left, right):
            return "B?"                                  # arithmetic on a truth value: always wrong
        return "Z" if left == right == "Z" else "R"
    return None


def assignment_type_error(spec, variable: str, expr) -> str:
    """Why ``variable := expr`` is ill-typed in ``spec``, or ``""`` if it is fine (or cannot be told)."""
    kinds = declared_kinds(spec)
    target = kinds.get(variable)
    got = value_kind(expr, kinds)
    if target is None or got is None:
        return ""
    if got == "B?":
        return (f"The expression does arithmetic on a truth value. {variable} is {_NAMES[target]}; "
                f"build its value from numbers and names of number type.")
    if target == "B" and got != "B":
        return (f"{variable} is a truth value (bool), but the expression is a number. Assign true, false, "
                f"or a test such as a < b or (x >= 8 && y = 2 * (y / 2)).")
    if target != "B" and got == "B":
        return (f"{variable} is {_NAMES[target]}, but the expression is a test (true or false). Assign a "
                f"numeric expression.")
    if target == "Z" and got == "R":
        return (f"{variable} is a whole number (int), but the expression can be a fraction (it uses a float "
                f"name or a decimal). Assign an integer-valued expression.")
    return ""
