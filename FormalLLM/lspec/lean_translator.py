"""Print a proof obligation as a Lean 4 theorem (Mathlib).

Same conventions as :mod:`lspec.coq_translator`, which this module reuses for
sorts and for the handling of undeclared names:

* ``int``/``nat`` -> ``ℤ`` (a ``nat`` variable gets a ``0 ≤ n`` hypothesis);
  ``float`` -> ``ℝ``; an undeclared name defaults to ``ℝ`` as in the Z3 translator;
* integer subterms used as reals are cast with ``(↑v : ℝ)`` at the *leaves*, so a
  cast never hides the relation between ``↑(N - i)`` and ``↑(N - (i + 1))``;
* ``/`` on ``ℤ`` is floor division ``Int.fdiv`` (to match Coq's ``Z.div``); on
  ``ℝ`` it is total field division (``x / 0 = 0``), unlike Z3's unspecified value.

Each conjunct of the assumptions becomes its own hypothesis ``h0, h1, ...``;
when integers and reals mix, each integer comparison is also supplied in lifted
form (``have hR0 : (↑a : ℝ) < ↑b := by exact_mod_cast h0``) so the linear
arithmetic over ``ℝ`` can use facts that were stated over ``ℤ``.
"""

from typing import Dict, List, Tuple

from FormalLLM.lspec.ast import (
    ArraySelect, ArraySlice, BinaryOp, BooleanConst, Const, NatType, Number,
    QuantifiedExpr, UnaryOp, Variable, VariablePreviousState,
)
from FormalLLM.lspec.coq_translator import (
    CoqPrinter, Env, UnsupportedForBackend, _ARITH, _CMP, _conjuncts,
    _type_defined_integers, sort_kind,
)

_TYPE = {"Z": "ℤ", "R": "ℝ"}
_LEAN_CMP = {"<": "<", "<=": "≤", ">": ">", ">=": "≥", "=": "="}


class LeanPrinter(CoqPrinter):
    """Same analysis as the Coq printer, different surface syntax."""

    def arith(self, e, target: str) -> str:
        k = self.kind_of(e)
        if k == "R" and target == "Z":
            raise UnsupportedForBackend("a real-valued term used where an integer is required")
        if isinstance(e, Number):
            return f"({e.value} : {_TYPE[target]})"
        if isinstance(e, (Variable, Const)):
            return self._lean_name(e.name, e.name, target)
        if isinstance(e, VariablePreviousState):
            return self._lean_name(self._prev_key(e.name), f"{e.name}0", target)
        if isinstance(e, UnaryOp) and e.op == "-":
            return f"(-{self.arith(e.expr, target)})"
        if isinstance(e, ArraySelect):
            self.used_arrays[e.array] = self.env.arrays.get(e.array, "R")
            text = f"({e.array} {self.arith(e.index, 'Z')})"
            return text if k == target else f"(↑{text} : ℝ)"
        if isinstance(e, BinaryOp) and e.op in _ARITH:
            if e.op == "/" and k == "Z":
                text = f"(Int.fdiv {self.arith(e.left, 'Z')} {self.arith(e.right, 'Z')})"
                return text if target == "Z" else f"(↑{text} : ℝ)"
            return f"({self.arith(e.left, target)} {e.op} {self.arith(e.right, target)})"
        raise UnsupportedForBackend(f"cannot print {type(e).__name__} as an arithmetic term")

    def _lean_name(self, key: str, shown: str, target: str) -> str:
        k = self._lookup(key)
        if not any(key in scope for scope in self.bound):
            self.used[shown] = k
        return shown if k == target else f"(↑{shown} : ℝ)"

    def prop(self, e) -> str:
        if isinstance(e, BooleanConst):
            return "True" if e.value else "False"
        if isinstance(e, UnaryOp) and e.op == "~":
            return f"(¬ {self.prop(e.expr)})"
        if isinstance(e, QuantifiedExpr):
            return self._lean_quantified(e)
        if isinstance(e, BinaryOp):
            if e.op == "/\\":
                return f"({self.prop(e.left)} ∧ {self.prop(e.right)})"
            if e.op == "\\/":
                return f"({self.prop(e.left)} ∨ {self.prop(e.right)})"
            if e.op in ("=", "<>") and (self.is_boolean(e.left) or self.is_boolean(e.right)):
                iff = f"({self.prop(e.left)} ↔ {self.prop(e.right)})"
                return iff if e.op == "=" else f"(¬ {iff})"
            if e.op in _CMP or e.op == "<>":
                kind = "R" if "R" in (self.kind_of(e.left), self.kind_of(e.right)) else "Z"
                left, right = self.arith(e.left, kind), self.arith(e.right, kind)
                if e.op == "<>":
                    return f"({left} ≠ {right})"
                return f"({left} {_LEAN_CMP[e.op]} {right})"
        if isinstance(e, (Variable, Const, VariablePreviousState)):
            if self._lookup(e.name) == "P":
                return self._proposition_variable(e)
            raise UnsupportedForBackend(f"{e.name!r} is a number, not a truth value")
        if isinstance(e, ArraySlice):
            raise UnsupportedForBackend("array slices are not supported")
        raise UnsupportedForBackend(f"cannot print {type(e).__name__} as a proposition")

    def _lean_quantified(self, q: QuantifiedExpr) -> str:
        scope: Dict[str, str] = {}
        binders, bounds = [], []
        for p in q.params:
            k = sort_kind(p.type_)
            if k is None:
                raise UnsupportedForBackend(f"quantifier over {p.type_!r} is not supported")
            scope[p.name] = k
            binders.append(f"({p.name} : {_TYPE[k]})")
            if isinstance(p.type_, NatType):
                bounds.append(f"(0 ≤ {p.name})")
        self.bound.append(scope)
        try:
            body = self.prop(q.expr)
        finally:
            self.bound.pop()
        guard = " ∧ ".join(bounds)
        if q.quantifier == "forall":
            if guard:
                body = f"({guard} → {body})"
            return f"(∀ {' '.join(binders)}, {body})"
        if guard:
            body = f"({guard} ∧ {body})"
        return f"(∃ {' '.join(binders)}, {body})"


def obligation_to_lean(obligation, name: str = "obl") -> Tuple[str, Dict[str, str], int]:
    """A complete theorem (without imports or proof) for ``obligation``.

    Returns ``(theorem_header, sorts, goal_conjuncts)`` where the header ends in
    ``:= by`` and ``goal_conjuncts`` is how many ``∧`` pieces the goal has.
    """
    env = Env(getattr(obligation, "params", []))
    printer = LeanPrinter(env)
    _type_defined_integers(env, printer, obligation.assumptions)

    hyps: List[str] = []
    lifts: List[Tuple[str, str]] = []             # (original hypothesis name, lifted statement)
    for assumption in obligation.assumptions:
        for conjunct in _conjuncts(assumption):
            hyps.append(printer.prop(conjunct))
    goal_parts = _conjuncts(obligation.goal)
    goal = " ∧ ".join(printer.prop(g) for g in goal_parts)

    sorts = dict(printer.used)
    nat_hyps = [f"(0 ≤ {n})" for n in env.nats if n in sorts]
    hyps = nat_hyps + hyps

    binders = []
    for kind in ("R", "Z", "P"):
        names = sorted(n for n, k in sorts.items() if k == kind)
        if names:
            binders.append(f"({' '.join(names)} : {_TYPE.get(kind, 'Prop')})")
    for array, elem in sorted(printer.used_arrays.items()):
        binders.append(f"({array} : ℤ → {_TYPE[elem]})")
    hyp_binders = [f"(h{i} : {h})" for i, h in enumerate(hyps)]

    header = f"theorem {name} {' '.join(binders)} {' '.join(hyp_binders)} :\n    {goal} := by"
    return header, sorts, len(goal_parts)
