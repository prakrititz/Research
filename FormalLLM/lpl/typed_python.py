"""Emit a derived program as Python that means what the prover meant.

The prover reads ``a / b`` on two integers as whole-number (floor) division and on anything else
as exact division. Python's ``/`` is always exact, so a program that was *proved* correct with
``n = 2 * (n / 2)`` as its evenness test is, executed as Python, a test that is always true:
``7 / 2`` is ``3.5`` and ``2 * 3.5`` is ``7.0``. :func:`to_python` in ``to_python.py`` knows
nothing about types; this module takes the declared types of the specification and emits ``//``
where both operands are integers, so the code that runs is the code that was verified.

    code = python_for(program, spec)
"""
from typing import Dict, Optional

from FormalLLM.lpl.ast import Assignment, IfElse, MixNode, SequentialComposition, Skip, While
from FormalLLM.lspec.ast import (
    ArraySelect, ArraySlice, ArrayType, BinaryOp, BooleanConst, BoolType, Const, Expr, FloatType,
    IntType, NatType, Number, QuantifiedExpr, Spec, UnaryOp, Variable, VariablePreviousState,
)

_ARITH = {"+", "-", "*", "/"}


def declared_kinds(spec: Spec) -> Dict[str, str]:
    """``name -> "Z" | "R" | "B"`` for every typed name of ``spec`` (arrays map to their element kind)."""
    kinds: Dict[str, str] = {}

    def kind_of_type(type_) -> Optional[str]:
        if isinstance(type_, ArrayType):
            return kind_of_type(type_.element_type)
        if isinstance(type_, (IntType, NatType)):
            return "Z"
        if isinstance(type_, FloatType):
            return "R"
        if isinstance(type_, BoolType):
            return "B"
        return None

    entries = list(spec.precondition.params) + list(spec.postcondition.params)
    entries += [entry for entry in (spec.frame or []) if hasattr(entry, "type_")]
    for entry in entries:
        kind = kind_of_type(entry.type_)
        if kind:
            kinds[entry.name] = kind
    return kinds


def _kind(expr: Expr, kinds: Dict[str, str]) -> str:
    if isinstance(expr, Number):
        return "R" if "." in str(expr.value) else "Z"
    if isinstance(expr, (Variable, Const)):
        return kinds.get(expr.name, "R")
    if isinstance(expr, VariablePreviousState):
        return kinds.get(expr.name, "R")
    if isinstance(expr, ArraySelect):
        return kinds.get(expr.array, "R")
    if isinstance(expr, UnaryOp) and expr.op == "-":
        return _kind(expr.expr, kinds)
    if isinstance(expr, BinaryOp) and expr.op in _ARITH:
        return "Z" if _kind(expr.left, kinds) == "Z" and _kind(expr.right, kinds) == "Z" else "R"
    return "B"


def expr_to_python(expr: Expr, kinds: Dict[str, str]) -> str:
    if isinstance(expr, BinaryOp):
        left, right = expr_to_python(expr.left, kinds), expr_to_python(expr.right, kinds)
        op = expr.op
        if op == "/":
            op = "//" if _kind(expr, kinds) == "Z" else "/"
        elif op == "/\\":
            op = "and"
        elif op == "\\/":
            op = "or"
        elif op == "=":
            op = "=="
        elif op == "<>":
            op = "!="
        return f"({left} {op} {right})"
    if isinstance(expr, UnaryOp):
        return f"({'not ' if expr.op == '~' else expr.op}{expr_to_python(expr.expr, kinds)})"
    if isinstance(expr, (Variable, Const)):
        return expr.name
    if isinstance(expr, Number):
        return str(expr.value)
    if isinstance(expr, BooleanConst):
        return str(bool(expr.value))
    if isinstance(expr, VariablePreviousState):
        return f"{expr.name}0"
    if isinstance(expr, ArraySelect):
        return f"{expr.array}[{expr_to_python(expr.index, kinds)}]"
    if isinstance(expr, ArraySlice):
        return f"{expr.array}[{expr_to_python(expr.start, kinds)}:{expr_to_python(expr.end, kinds)}]"
    if isinstance(expr, QuantifiedExpr):
        raise NotImplementedError("quantified expressions cannot be executed")
    raise ValueError(f"unknown expression type: {type(expr)}")


def program_to_python(node: MixNode, kinds: Dict[str, str], indent: int = 0) -> str:
    pad = "    " * indent
    if node is None or isinstance(node, Skip):
        return f"{pad}pass"
    if isinstance(node, Assignment):
        return f"{pad}{node.variable} = {expr_to_python(node.expr, kinds)}"
    if isinstance(node, SequentialComposition):
        return f"{program_to_python(node.first, kinds, indent)}\n{program_to_python(node.second, kinds, indent)}"
    if isinstance(node, IfElse):
        return (f"{pad}if {expr_to_python(node.guard, kinds)}:\n"
                f"{program_to_python(node.then_branch, kinds, indent + 1)}\n"
                f"{pad}else:\n"
                f"{program_to_python(node.else_branch, kinds, indent + 1)}")
    if isinstance(node, While):
        return (f"{pad}while {expr_to_python(node.guard, kinds)}:\n"
                f"{program_to_python(node.body, kinds, indent + 1)}")
    if isinstance(node, Spec):
        raise ValueError("cannot execute an unresolved specification")
    raise ValueError(f"unknown program node: {type(node)}")


_DEFAULT = {"Z": "0", "R": "0.0", "B": "False"}


def free_frame_initialisation(spec: Spec) -> str:
    """Start values for the frame variables whose value on entry the specification leaves arbitrary.

    In the refinement calculus every variable always holds *some* value, so a derivation may read a frame
    variable before assigning it (the proof holds whatever the value was). Python has no value before the
    first assignment. Measured (v8, integer division): a proved program began with ``r := n - q * d`` and
    crashed with ``NameError: q`` on every input. Giving such a variable any value is sound, because the
    proof covers every starting value; a variable the precondition constrains (``i = 0``) is left to the
    caller, who must establish the precondition.
    """
    from FormalLLM.refinement.frame import frame_names
    from FormalLLM.refinement.relevance import entry_value_matters
    kinds = declared_kinds(spec)
    lines = [f"{name} = {_DEFAULT.get(kinds.get(name), '0')}"
             for name in sorted(frame_names(spec.frame))
             if not entry_value_matters(spec, name)]
    return "\n".join(lines)


def python_for(program: MixNode, spec: Spec) -> str:
    """The Python for ``program``, with whole-number division wherever the spec's types call for it.

    Frame variables whose entry value is arbitrary are given a start value first (see
    :func:`free_frame_initialisation`), so the program never reads a name Python has not bound.
    """
    body = program_to_python(program, declared_kinds(spec))
    start = free_frame_initialisation(spec)
    return f"{start}\n{body}" if start else body
