"""Readable, re-parseable rendering of L_spec for prompts and failure feedback.

Why this exists
---------------
``prompts.to_string`` parenthesises every binary operator, so a loop-body
specification reached the model as::

    ((((N >= 0) /\\ (e > 0)) /\\ ((x * x) <= N)) /\\ (((x + e) * (x + e)) <= N)) /\\ ...

and it spelled the variant's starting value as ``N0 - ((x0 + e0) * (x0 + e0))``
-- previous-state copies even of constants that never change. A reasoning model
spent its first paragraph deciding the specification was "weird", then
abandoned the obvious one-assignment body for a chain of structural laws
(measured: 27 of 40 LLM calls on the paper's square-root example).

This module renders the same formulas the way a person would write them:

* minimal parentheses, with the operator spellings the model is asked to use
  (``&&``, ``||``, ``!``, ``!=``), so what it reads and what it writes agree;
* conjunctions as bullet lists, one fact per line;
* the loop variant's starting value as a single named constant ``V0``;
* the frame and the declared constants stated up front.

Everything here is presentation. Nothing in the engine reads these strings, and
``to_string`` is unchanged, so progress checking and traces are unaffected.

Re-parseability matters: ``~`` and ``/\\`` in L_spec share one precedence level
and ``~`` extends as far right as it can (``~a /\\ b`` is ``~(a /\\ b)``), so a
negation inside a conjunction is always parenthesised here.
"""

import re
from typing import Dict, List, Optional, Sequence, Tuple

from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import (
    ArraySelect, ArraySlice, ArrayType, BinaryOp, BooleanConst, BoolType,
    CharType, Const, Definition, Expr, FloatType, IntType, NatType, Number,
    Param, QuantifiedExpr, Spec, UnaryOp, Variable, VariablePreviousState,
)

# Precedence levels (higher binds tighter).
_P_QUANT, _P_LOGIC, _P_NOT, _P_CMP, _P_ADD, _P_MUL, _P_NEG, _P_ATOM = 1, 2, 3, 4, 5, 6, 7, 9

_ARITH_PREC = {"+": _P_ADD, "-": _P_ADD, "*": _P_MUL, "/": _P_MUL}
_CMP_OPS = {"<", "<=", "=", ">", ">=", "<>"}
_LOGIC_OPS = {"/\\", "\\/"}
_DISPLAY = {"/\\": "&&", "\\/": "||", "<>": "!="}


def type_name(t) -> str:
    if isinstance(t, ArrayType):
        return f"array {type_name(t.element_type)}"
    if isinstance(t, BoolType):
        return "bool"
    if isinstance(t, NatType):
        return "nat"
    if isinstance(t, IntType):
        return "int"
    if isinstance(t, FloatType):
        return "float"
    if isinstance(t, CharType):
        return "char"
    return "?" if t is None else str(t)


def _prec(node) -> int:
    if isinstance(node, BinaryOp):
        if node.op in _ARITH_PREC:
            return _ARITH_PREC[node.op]
        if node.op in _CMP_OPS:
            return _P_CMP
        return _P_LOGIC
    if isinstance(node, UnaryOp):
        # L_spec's unary minus takes the whole expression to its right
        # (`atom: "-" expr`), so `-a < b` parses as `-(a < b)`. Giving it the
        # lowest precedence makes every enclosing operator parenthesise it.
        return _P_NOT if node.op == "~" else 0
    if isinstance(node, QuantifiedExpr):
        return _P_QUANT
    if isinstance(node, Number) and str(node.value).startswith("-"):
        return _P_NEG
    return _P_ATOM


def _divides(node) -> bool:
    """Does a chain of ``*`` and ``/`` contain a division? (Such a chain cannot be regrouped.)"""
    return (isinstance(node, BinaryOp) and node.op in ("*", "/")
            and (node.op == "/" or _divides(node.left) or _divides(node.right)))


def _wrap(text: str, needs: bool) -> str:
    return f"({text})" if needs else text


def render_expr(node) -> str:
    """One formula as a single line, with minimal parentheses."""
    if isinstance(node, (Variable, Const)):
        return node.name
    if isinstance(node, VariablePreviousState):
        return f"{node.name}0"
    if isinstance(node, Number):
        return str(node.value)
    if isinstance(node, BooleanConst):
        return "true" if node.value else "false"
    if isinstance(node, ArraySelect):
        return f"{node.array}[{render_expr(node.index)}]"
    if isinstance(node, ArraySlice):
        return f"{node.array}[{render_expr(node.start)}:{render_expr(node.end)}]"
    if isinstance(node, UnaryOp):
        if node.op == "~":
            inner = node.expr
            return "!" + _wrap(render_expr(inner), _prec(inner) < _P_ATOM)
        inner = node.expr
        return "-" + _wrap(render_expr(inner), _prec(inner) < _P_ATOM)
    if isinstance(node, QuantifiedExpr):
        binders = "".join(f"({p.name}:{type_name(p.type_)})" for p in node.params)
        return f"{node.quantifier} {binders} {render_expr(node.expr)}"
    if isinstance(node, BinaryOp):
        op = node.op
        left, right = node.left, node.right
        if op in _ARITH_PREC:
            p = _ARITH_PREC[op]
            l_text = _wrap(render_expr(left), _prec(left) < p)
            # Same-level right operands need parentheses when regrouping would change the value:
            # a - (b + c), a / (b * c) -- and a * (b / c), because "/" on integers is whole-number
            # division, so 2 * (n / 2) ("n is even") is not 2 * n / 2 (always n).
            r_paren = _prec(right) < p or (_prec(right) == p and (
                op in ("-", "/") or (op == "*" and _divides(right))))
            return f"{l_text} {op} {_wrap(render_expr(right), r_paren)}"
        if op in _CMP_OPS:
            l_text = _wrap(render_expr(left), _prec(left) <= _P_CMP)
            r_text = _wrap(render_expr(right), _prec(right) <= _P_CMP)
            return f"{l_text} {_DISPLAY.get(op, op)} {r_text}"
        if op in _LOGIC_OPS:
            def side(child) -> str:
                same = isinstance(child, BinaryOp) and child.op == op
                # Comparisons bind tighter and need no parentheses; a negation,
                # a quantifier or the *other* connective must be wrapped because
                # L_spec gives /\ and \/ one level and lets ~ run to the right.
                loose = (isinstance(child, (UnaryOp, QuantifiedExpr)) and
                         not (isinstance(child, UnaryOp) and child.op == "-")) \
                    or (isinstance(child, BinaryOp) and child.op in _LOGIC_OPS and not same)
                return _wrap(render_expr(child), loose)
            return f"{side(left)} {_DISPLAY[op]} {side(right)}"
    raise walk.UnknownNodeError(node)


def conjuncts(expr) -> List:
    """The conjuncts of ``expr``, flattened through nested ``/\\``."""
    if isinstance(expr, BinaryOp) and expr.op == "/\\":
        return conjuncts(expr.left) + conjuncts(expr.right)
    return [expr]


def render_conjuncts(expr) -> List[str]:
    return [render_expr(c) for c in conjuncts(expr)]


def bullets(expr, indent: str = "  ") -> str:
    """A formula as a bullet list, one conjunct per line."""
    return "\n".join(f"{indent}- {line}" for line in render_conjuncts(expr))


# --- previous-state abbreviation ------------------------------------------

def _previous_state(node):
    """``node`` with every variable renamed to its previous-state twin."""
    if isinstance(node, (Variable, Const)):
        return VariablePreviousState(node.name)
    return walk.map_children(node, _previous_state)


def _mentions_previous_state(node) -> bool:
    if isinstance(node, VariablePreviousState):
        return True
    return any(_mentions_previous_state(c) for c in walk.children(node))


def _replace(node, target, replacement):
    if node == target:
        return replacement
    return walk.map_children(node, lambda c: _replace(c, target, replacement))


def find_variant_starts(exprs: Sequence) -> List[Tuple[Expr, Expr]]:
    """Conjuncts of the form ``E = E0``, where ``E0`` is ``E`` at loop entry.

    The loop laws state "the variant starts at ``V0``" as ``V = V0'`` where
    ``V0'`` is ``V`` with every name renamed to its previous-state twin. Returns
    ``(V, V0')`` pairs in order of appearance, without duplicates.
    """
    found: List[Tuple[Expr, Expr]] = []
    for expr in exprs:
        for c in conjuncts(expr):
            if (isinstance(c, BinaryOp) and c.op == "="
                    and _mentions_previous_state(c.right)
                    and not _mentions_previous_state(c.left)
                    and _previous_state(c.left) == c.right
                    and all(c.right != old for _, old in found)):
                found.append((c.left, c.right))
    return found


_VARIANT_NAME = re.compile(r"^V\d+$")


def named_variant_starts(exprs: Sequence) -> Dict[str, Expr]:
    """``{V0: E}`` for conjuncts ``E = V0`` -- the loop laws' own name for the variant's start."""
    found: Dict[str, Expr] = {}
    for expr in exprs:
        for c in conjuncts(expr):
            if (isinstance(c, BinaryOp) and c.op == "="
                    and isinstance(c.right, (Variable, Const))
                    and _VARIANT_NAME.match(c.right.name)
                    and not isinstance(c.left, (Variable, Const))):
                found.setdefault(c.right.name, c.left)
    return found


def abbreviate_variant_starts(exprs: Sequence) -> Tuple[List, Dict[str, Tuple[Expr, Expr]]]:
    """Replace each variant-start expression by a named constant ``V0``, ``V1`` ...

    Returns the rewritten formulas and ``{name: (V, V0')}`` so a caller can
    explain the name and, for a counterexample, evaluate it.
    """
    pairs = find_variant_starts(exprs)
    if not pairs:
        return list(exprs), {}
    names: Dict[str, Tuple[Expr, Expr]] = {}
    out = list(exprs)
    for i, (variant, start) in enumerate(pairs):
        name = f"V{i}"
        names[name] = (variant, start)
        out = [_replace(e, start, Variable(name)) for e in out]
    return out, names


def apply_abbreviations(expr, names: Dict[str, Tuple[Expr, Expr]]):
    """``expr`` with each variant-start expression replaced by its name."""
    for name, (_variant, start) in names.items():
        expr = _replace(expr, start, Variable(name))
    return expr


def mentioned_names(expr) -> set:
    """Every name ``expr`` shows when rendered, previous-state twins included (``x0``)."""
    if isinstance(expr, (Variable, Const)):
        return {expr.name}
    if isinstance(expr, VariablePreviousState):
        return {f"{expr.name}0"}
    found = set()
    for attr, kind in walk.schema_of(expr):
        if kind == walk.NAME:
            found.add(getattr(expr, attr))
    for child in walk.children(expr):
        found |= mentioned_names(child)
    # A bound name is not a free variable of the formula.
    return found - {p.name for p in walk.binders_of(expr)}


def explain_variant_starts(names: Dict[str, Tuple[Expr, Expr]]) -> List[str]:
    return [f"{name} is the value of {render_expr(variant)} when the loop body starts"
            for name, (variant, _start) in names.items()]


# --- specifications --------------------------------------------------------

def _frame_entries(spec) -> List[Tuple[str, Optional[object]]]:
    out = []
    for entry in (spec.frame or []):
        out.append((getattr(entry, "name", str(entry)), getattr(entry, "type_", None)))
    return out


def constants_of(spec) -> List[Param]:
    """Declared names that are not in the frame, deduplicated, in order."""
    frame = {name for name, _ in _frame_entries(spec)}
    seen, out = set(), []
    for p in list(spec.precondition.params) + list(spec.postcondition.params):
        if p.name not in frame and p.name not in seen:
            seen.add(p.name)
            out.append(p)
    return out


def render_spec(spec: Spec) -> str:
    """A specification as a readable block."""
    (pre, post), names = abbreviate_variant_starts(
        [spec.precondition.expr, spec.postcondition.expr])

    lines: List[str] = []
    frame = _frame_entries(spec)
    if frame:
        shown = ", ".join(n if t is None else f"{n}:{type_name(t)}" for n, t in frame)
        lines.append(f"Frame (the only names the program may assign): {shown}")
    consts = constants_of(spec)
    if consts:
        shown = ", ".join(f"{p.name}:{type_name(p.type_)}" for p in consts)
        lines.append(f"Constants (never assigned): {shown}")
    lines.append("Precondition P (may be assumed on entry):")
    lines.append(bullets(pre))
    lines.append("Postcondition Q (must hold on exit):")
    lines.append(bullets(post))
    for note in explain_variant_starts(names):
        lines.append(f"Note: {note}.")
    for name, variant in named_variant_starts([spec.precondition.expr,
                                               spec.postcondition.expr]).items():
        lines.append(f"Note: {name} is the value of {render_expr(variant)} when the loop body starts.")
    return "\n".join(lines)


def render_spec_compact(spec: Spec) -> str:
    """``[P, Q]`` on one line, for history and feedback."""
    (pre, post), _ = abbreviate_variant_starts(
        [spec.precondition.expr, spec.postcondition.expr])
    return f"[ {render_expr(pre)} ,  {render_expr(post)} ]"
