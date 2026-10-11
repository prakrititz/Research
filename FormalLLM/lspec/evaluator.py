"""Evaluate L_spec formulas on concrete values.

Why this exists. A formal specification written by hand for a benchmark problem can be
wrong, and a wrong specification makes every later result meaningless: a program "proved
correct" against the wrong specification is correct for the wrong problem. The check that
catches this is cheap and does not need a prover: run the problem's *reference solution* on
its test inputs, and require that the specification's precondition holds on each input and
its postcondition holds on each (input, reference output) pair. A specification that the
reference solution violates is wrong. (A specification that is merely too weak passes
this check; that weakness is measured separately, by mutating the reference outputs.)

Semantics, chosen to agree with the prover's:

* ``/`` on two integers is whole-number (floor) division; any other ``/`` is exact.
* an array read out of range, or a division by zero, is *undefined*: it raises
  :class:`Undefined` unless a short-circuiting ``/\\`` or ``\\/`` skips it, which is how
  specifications guard their reads (``i < 0 \\/ i >= n \\/ a[i] ...``).
* ``forall``/``exists`` over an integer binder range over a finite window large enough for
  the values at hand (twice the largest magnitude or length, plus two); over a real binder
  they cannot be enumerated and raise :class:`EvaluationError`.
"""

import math
from typing import Any, Dict, Optional

from FormalLLM.lspec.ast import (
    ArraySelect, ArraySlice, BinaryOp, BooleanConst, Const, FloatType, Number,
    QuantifiedExpr, UnaryOp, Variable, VariablePreviousState,
)

#: Most values a single quantifier will try. Past this the answer is "cannot tell", not a guess:
#: a specification quantifying over a range of a million values is checked by the prover, not here.
MAX_ITERATIONS = 200_000


class EvaluationError(Exception):
    """The formula cannot be evaluated on these values."""


class Undefined(EvaluationError):
    """The formula has no value here (array read out of range, division by zero)."""


def _magnitude(env: Dict[str, Any]) -> int:
    best = 1
    for value in env.values():
        if isinstance(value, bool):
            continue
        if isinstance(value, (int, float)):
            best = max(best, int(abs(value)))
        elif isinstance(value, (list, tuple)):
            best = max(best, len(value))
            for item in value:
                if isinstance(item, (int, float)) and not isinstance(item, bool):
                    best = max(best, int(abs(item)))
    return best


def _is_whole(v) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _declared_floats(spec):
    """Names declared ``float`` (scalars) and ``array float`` (arrays) anywhere in ``spec``."""
    from FormalLLM.lspec.ast import ArrayType
    scalars, arrays = set(), set()
    params = list(spec.precondition.params) + list(spec.postcondition.params) + list(spec.frame or [])
    for p in params:
        type_ = getattr(p, "type_", None)                   # an untyped frame entry has none
        if isinstance(type_, FloatType):
            scalars.add(p.name)
            scalars.add(f"{p.name}0")                       # its value before the step (x0) is a float too
        elif isinstance(type_, ArrayType) and isinstance(type_.element_type, FloatType):
            arrays.add(p.name)
    return scalars, arrays


def _as_declared(spec, env: Dict[str, Any]) -> Dict[str, Any]:
    """``env`` with every value of a ``float`` name made a float.

    A test passes ``triangle_area(5, 3)`` with Python ints, but the specification declares the
    sides ``float``, and the prover reads them as reals: ``5 * 3 / 2`` is 7.5, not 7. Deciding the
    division from the runtime values instead of the declared types got the reference answer wrong.
    """
    scalars, arrays = _declared_floats(spec)
    out = dict(env)
    for name, value in env.items():
        if name in scalars and isinstance(value, int):           # bool too: Python reads True as 1
            out[name] = float(value)
        elif name in arrays and isinstance(value, (list, tuple)):
            out[name] = [float(v) if isinstance(v, int) else v for v in value]
    return out


def evaluate(expr, env: Dict[str, Any]):
    """The value of ``expr`` when its names are bound as in ``env``."""
    if isinstance(expr, Number):
        text = str(expr.value)
        return float(text) if "." in text else int(text)
    if isinstance(expr, BooleanConst):
        return bool(expr.value)
    if isinstance(expr, (Variable, Const)):
        if expr.name not in env:
            raise EvaluationError(f"no value for {expr.name!r}")
        return env[expr.name]
    if isinstance(expr, VariablePreviousState):
        for key in (f"{expr.name}0", expr.name + "_prev"):
            if key in env:
                return env[key]
        raise EvaluationError(f"no previous value for {expr.name!r} (expected {expr.name + '0'!r} in the environment)")
    if isinstance(expr, UnaryOp):
        value = evaluate(expr.expr, env)
        if expr.op == "~":
            return not value
        if expr.op == "-":
            return -value
        raise EvaluationError(f"unknown unary operator {expr.op!r}")
    if isinstance(expr, ArraySelect):
        array = _array(expr.array, env)
        index = evaluate(expr.index, env)
        if not _is_whole(index) or not 0 <= index < len(array):
            raise Undefined(f"{expr.array}[{index}] is out of range (length {len(array)})")
        return array[index]
    if isinstance(expr, ArraySlice):
        array = _array(expr.array, env)
        lo, hi = evaluate(expr.start, env), evaluate(expr.end, env)
        if not (_is_whole(lo) and _is_whole(hi)) or lo < 0 or hi > len(array) or lo > hi:
            raise Undefined(f"{expr.array}[{lo}:{hi}] is out of range (length {len(array)})")
        return list(array[lo:hi])
    if isinstance(expr, QuantifiedExpr):
        return _quantified(expr, env)
    if isinstance(expr, BinaryOp):
        return _binary(expr, env)
    raise EvaluationError(f"cannot evaluate {type(expr).__name__}")


def _array(name: str, env: Dict[str, Any]):
    if name not in env:
        raise EvaluationError(f"no value for array {name!r}")
    value = env[name]
    if not isinstance(value, (list, tuple)):
        raise EvaluationError(f"{name!r} is not an array")
    return value


def _binary(expr: BinaryOp, env: Dict[str, Any]):
    op = expr.op
    if op == "/\\":                       # short-circuiting, so guards protect later reads
        return bool(evaluate(expr.left, env)) and bool(evaluate(expr.right, env))
    if op == "\\/":
        return bool(evaluate(expr.left, env)) or bool(evaluate(expr.right, env))
    left, right = evaluate(expr.left, env), evaluate(expr.right, env)
    if op == "+":
        return left + right
    if op == "-":
        return left - right
    if op == "*":
        return left * right
    if op == "/":
        if right == 0:
            raise Undefined("division by zero")
        if _is_whole(left) and _is_whole(right):
            return left // right
        return left / right
    if op == "<":
        return left < right
    if op == "<=":
        return left <= right
    if op == ">":
        return left > right
    if op == ">=":
        return left >= right
    if op == "=":
        return left == right
    if op == "<>":
        return left != right
    raise EvaluationError(f"unknown operator {op!r}")


def _mentions(node, name: str) -> bool:
    from FormalLLM.lspec import walk
    if isinstance(node, (Variable, Const)) and node.name == name:
        return True
    if isinstance(node, VariablePreviousState) and node.name == name:
        return True
    names = walk.names_of(node) if walk.is_registered(node) else []
    if name in names:
        return True
    return any(_mentions(child, name) for child in walk.children(node))


def _chain(expr, op: str):
    """The operands of a left- or right-nested chain of one connective, flattened into a list."""
    if isinstance(expr, BinaryOp) and expr.op == op:
        return _chain(expr.left, op) + _chain(expr.right, op)
    return [expr]


def _bounds_from(parts, name: str, env: Dict[str, Any], guards_exclude: bool):
    """Integer bounds ``(lo, hi)`` on ``name`` that the comparisons in ``parts`` imply.

    For ``exists`` the parts are the conjuncts (``0 <= k``, ``k < n`` restrict k); for ``forall``
    they are the disjuncts (``k < 0``, ``k >= n`` make the body true outside [0, n), so only that
    interval needs checking). Anything else contributes no bound.
    """
    lo = hi = None
    for part in parts:
        if not (isinstance(part, BinaryOp) and part.op in ("<", "<=", ">", ">=", "=")):
            continue
        left_is_k = isinstance(part.left, (Variable, Const)) and part.left.name == name
        right_is_k = isinstance(part.right, (Variable, Const)) and part.right.name == name
        if left_is_k == right_is_k:
            continue
        other = part.right if left_is_k else part.left
        if _mentions(other, name):
            continue
        try:
            value = evaluate(other, env)
        except EvaluationError:
            continue
        op = part.op if left_is_k else {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "=": "="}[part.op]   # as "k op value"
        if guards_exclude:       # the part makes the body true; the body must be checked where it is false
            op = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "=": "<>"}[op]
            if op == "<>":
                continue
        if op == "=":
            lo = value if lo is None else max(lo, value)
            hi = value if hi is None else min(hi, value)
        elif op == "<":
            hi = math.ceil(value) - 1 if hi is None else min(hi, math.ceil(value) - 1)
        elif op == "<=":
            hi = math.floor(value) if hi is None else min(hi, math.floor(value))
        elif op == ">":
            lo = math.floor(value) + 1 if lo is None else max(lo, math.floor(value) + 1)
        elif op == ">=":
            lo = math.ceil(value) if lo is None else max(lo, math.ceil(value))
    return lo, hi


def _quantified(expr: QuantifiedExpr, env: Dict[str, Any]) -> bool:
    window = _magnitude(env) + 2           # how far an *unbounded* side is searched

    def search(position: int, scope: Dict[str, Any]) -> bool:
        if position == len(expr.params):
            return bool(evaluate(expr.expr, scope))
        param = expr.params[position]
        if isinstance(param.type_, FloatType):
            raise EvaluationError(f"cannot enumerate the real-valued binder {param.name!r}")
        # the bounds the formula itself states (the guards of a bounded quantification)
        if expr.quantifier == "forall":
            parts = _chain(expr.expr, "\\/")
            lo, hi = _bounds_from(parts, param.name, scope, guards_exclude=True)
        else:
            parts = _chain(expr.expr, "/\\")
            lo, hi = _bounds_from(parts, param.name, scope, guards_exclude=False)
        lo = -window if lo is None else lo
        hi = window if hi is None else hi
        if hi - lo + 1 > MAX_ITERATIONS:
            raise EvaluationError(f"too many values to enumerate {param.name!r} ({hi - lo + 1})")
        results = (search(position + 1, {**scope, param.name: value}) for value in range(lo, hi + 1))
        return all(results) if expr.quantifier == "forall" else any(results)

    return search(0, dict(env))


def holds(definition, env: Dict[str, Any]) -> bool:
    """Does a pre/postcondition (a ``Definition``) hold on ``env``?"""
    return bool(evaluate(definition.expr, env))


def check_specification(spec, inputs: Dict[str, Any], outputs: Dict[str, Any],
                        previous: Optional[Dict[str, Any]] = None) -> Optional[str]:
    """``None`` if (inputs, outputs) satisfy ``spec``; otherwise a sentence saying what failed.

    ``previous`` binds the pre-state of frame variables (``x0``) for specifications that talk
    about it.
    """
    pre_env = dict(inputs)
    if previous:
        pre_env.update(previous)
    pre_env = _as_declared(spec, pre_env)
    try:
        if not holds(spec.precondition, pre_env):
            return "the precondition is false on this input"
    except EvaluationError as error:
        return f"the precondition cannot be evaluated: {error}"
    post_env = _as_declared(spec, {**pre_env, **outputs})
    try:
        if not holds(spec.postcondition, post_env):
            return "the postcondition is false for the reference output"
    except EvaluationError as error:
        return f"the postcondition cannot be evaluated: {error}"
    return None
