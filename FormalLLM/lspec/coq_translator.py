"""Print a proof obligation as a Coq/Rocq goal.

The obligation ``assumptions |- goal`` becomes::

    Goal forall (N e x : R), N >= 0 -> e > 0 -> ... -> goal.

Sorts follow the same convention as :mod:`lspec.z3_translator`, so the two
backends are talking about the same statement:

* ``int`` / ``nat`` -> ``Z``; ``float`` -> ``R`` (the reals);
* an undeclared name defaults to ``R``, exactly as in the Z3 translator;
* previous-state names (``x0``) get the sort of ``x``;
* arrays are functions ``Z -> Z`` (or ``Z -> R``); slices are unsupported.

Where the two worlds differ, the difference is stated rather than hidden:

* ``nat`` is *really* non-negative here (a hypothesis ``0 <= n`` per free
  ``nat`` variable; ``forall``/``exists`` over a ``nat`` carry the bound). The
  Z3 translator treats ``nat`` as plain ``Int``.
* ``/`` on ``Z`` is floor division ``Z.div``; on ``R`` it is field division,
  which Coq makes total (``x / 0 = 0``). Z3 leaves ``x / 0`` unspecified.
  Neither affects obligations that never divide by something that may be zero.

Mixing integers and reals inserts ``IZR`` casts, as in the Z3 translator's
implicit coercion. Anything that cannot be printed raises
:class:`UnsupportedForBackend`; nothing is silently dropped.
"""

from typing import Dict, List, Optional, Tuple

from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import (
    ArraySelect, ArraySlice, ArrayType, BinaryOp, BooleanConst, BoolType, Const,
    FloatType, IntType, NatType, Number, QuantifiedExpr, UnaryOp, Variable,
    VariablePreviousState,
)


class UnsupportedForBackend(Exception):
    """The obligation uses a construct this backend does not translate."""


_ARITH = {"+", "-", "*", "/"}
_CMP = {"<": "<", "<=": "<=", ">": ">", ">=": ">=", "=": "="}


def sort_kind(type_) -> Optional[str]:
    """``"Z"``, ``"R"`` or ``None`` (unsupported) for a declared L_spec type."""
    if isinstance(type_, (IntType, NatType)):
        return "Z"
    if isinstance(type_, FloatType):
        return "R"
    return None


class Env:
    """Declared sorts of the names an obligation mentions."""

    def __init__(self, params):
        self.kind: Dict[str, str] = {}
        self.arrays: Dict[str, str] = {}      # name -> element kind
        self.nats: List[str] = []
        #: Boolean variables. They are printed as propositional variables (``t : Prop``): ``t = true``
        #: becomes ``t``, ``t = false`` becomes ``~ t``, and an assignment ``t := C`` substitutes the
        #: proposition ``C`` for ``t``, which is exactly what the obligation means.
        self.props: set = set()
        for p in params or []:
            if isinstance(p.type_, ArrayType):
                elem = sort_kind(p.type_.element_type)
                if elem is None:
                    raise UnsupportedForBackend(f"array of {p.type_.element_type!r} is not supported")
                self.arrays[p.name] = elem
            elif isinstance(p.type_, BoolType):
                self.props.add(p.name)
            else:
                k = sort_kind(p.type_)
                if k is None:
                    continue                    # untyped frame entries default to R below
                self.kind[p.name] = k
                if isinstance(p.type_, NatType):
                    self.nats.append(p.name)

    def of(self, name: str) -> str:
        if name in self.props:
            return "P"
        return self.kind.get(name, "R")


def _scope(kind: str) -> str:
    return f"%{kind}"


class CoqPrinter:
    def __init__(self, env: Env):
        self.env = env
        self.used: Dict[str, str] = {}            # variable name -> kind, for the binder list
        self.used_arrays: Dict[str, str] = {}
        self.bound: List[Dict[str, str]] = []     # quantifier scopes

    # --- sorts ----------------------------------------------------------------

    def _lookup(self, name: str) -> str:
        for scope in reversed(self.bound):
            if name in scope:
                return scope[name]
        return self.env.of(name)

    def _prev_key(self, name: str) -> str:
        """The name whose sort ``name`` + ``0`` has.

        ``x0`` is usually the previous value of ``x`` and shares its sort, but the
        loop laws' ``V0`` is a plain name, and a model that writes ``V0`` gets it
        parsed as "the previous value of V". Both denote the same solver symbol,
        so if a sort is recorded for the spelt-out ``V0`` it wins.
        """
        spelt = f"{name}0"
        return spelt if spelt in self.env.kind else name

    def _numeric(self, key: str) -> str:
        kind = self._lookup(key)
        if kind == "P":
            raise UnsupportedForBackend(f"{key!r} is a truth value, not a number")
        return kind

    def kind_of(self, e) -> str:
        if isinstance(e, Number):
            return "R" if "." in str(e.value) else "Z"
        if isinstance(e, (Variable, Const)):
            return self._numeric(e.name)
        if isinstance(e, VariablePreviousState):
            return self._numeric(self._prev_key(e.name))
        if isinstance(e, UnaryOp) and e.op == "-":
            return self.kind_of(e.expr)
        if isinstance(e, ArraySelect):
            return self.env.arrays.get(e.array, "R")
        if isinstance(e, BinaryOp) and e.op in _ARITH:
            return "R" if "R" in (self.kind_of(e.left), self.kind_of(e.right)) else "Z"
        raise UnsupportedForBackend(f"cannot give a numeric sort to {type(e).__name__}")

    # --- arithmetic -----------------------------------------------------------

    def arith(self, e, target: str) -> str:
        k = self.kind_of(e)
        if k == "R" and target == "Z":
            raise UnsupportedForBackend("a real-valued term used where an integer is required")
        if isinstance(e, Number):
            if target == "Z":
                return f"({e.value})%Z"
            text = str(e.value)
            return f"({text})%R"
        if isinstance(e, (Variable, Const)):
            return self._name(e.name, e.name, target)
        if isinstance(e, VariablePreviousState):
            return self._name(self._prev_key(e.name), f"{e.name}0", target)
        if isinstance(e, UnaryOp) and e.op == "-":
            return f"(-{self.arith(e.expr, target)}){_scope(target)}"
        if isinstance(e, ArraySelect):
            self.used_arrays[e.array] = self.env.arrays.get(e.array, "R")
            text = f"({e.array} {self.arith(e.index, 'Z')})"
            return text if k == target else f"(IZR {text})"
        if isinstance(e, BinaryOp) and e.op in _ARITH:
            if e.op == "/" and k == "Z":
                # Whole-number division has no counterpart on the reals: keep it
                # opaque and cast its result.
                text = f"(Z.div {self.arith(e.left, 'Z')} {self.arith(e.right, 'Z')})"
                return text if target == "Z" else f"(IZR {text})"
            # IZR is a ring homomorphism, so for + - * a cast is pushed down to the
            # leaves instead of wrapping the whole term. A single opaque
            # `IZR (N - i)` hides its relation to `IZR (N - (i + 1))` from lra/nra.
            left, right = self.arith(e.left, target), self.arith(e.right, target)
            return f"({left} {e.op} {right}){_scope(target)}"
        raise UnsupportedForBackend(f"cannot print {type(e).__name__} as an arithmetic term")

    def _name(self, key: str, shown: str, target: str) -> str:
        k = self._lookup(key)
        if not any(key in scope for scope in self.bound):
            self.used[shown] = k
        return shown if k == target else f"(IZR {shown})"

    # --- propositions ---------------------------------------------------------

    def is_boolean(self, e) -> bool:
        """Is ``e`` a truth value (a proposition) rather than a number?"""
        if isinstance(e, BooleanConst):
            return True
        if isinstance(e, (Variable, Const, VariablePreviousState)):
            return self._lookup(e.name) == "P"
        if isinstance(e, UnaryOp):
            return e.op == "~"
        if isinstance(e, QuantifiedExpr):
            return True
        return isinstance(e, BinaryOp) and (e.op in ("/\\", "\\/", "<>") or e.op in _CMP)

    def _proposition_variable(self, e) -> str:
        shown = f"{e.name}0" if isinstance(e, VariablePreviousState) else e.name
        if not any(e.name in scope for scope in self.bound):
            self.used[shown] = "P"
        return shown

    def prop(self, e) -> str:
        if isinstance(e, BooleanConst):
            return "True" if e.value else "False"
        if isinstance(e, UnaryOp) and e.op == "~":
            return f"(~ {self.prop(e.expr)})"
        if isinstance(e, QuantifiedExpr):
            return self._quantified(e)
        if isinstance(e, BinaryOp):
            if e.op == "/\\":
                return f"({self.prop(e.left)} /\\ {self.prop(e.right)})"
            if e.op == "\\/":
                return f"({self.prop(e.left)} \\/ {self.prop(e.right)})"
            if e.op in ("=", "<>") and (self.is_boolean(e.left) or self.is_boolean(e.right)):
                iff = f"({self.prop(e.left)} <-> {self.prop(e.right)})"
                return iff if e.op == "=" else f"(~ {iff})"
            if e.op in _CMP or e.op == "<>":
                kind = "R" if "R" in (self.kind_of(e.left), self.kind_of(e.right)) else "Z"
                left, right = self.arith(e.left, kind), self.arith(e.right, kind)
                if e.op == "<>":
                    return f"(~ ({left} = {right}){_scope(kind)})"
                return f"({left} {_CMP[e.op]} {right}){_scope(kind)}"
        if isinstance(e, (Variable, Const, VariablePreviousState)):
            if self._lookup(e.name) == "P":
                return self._proposition_variable(e)
            raise UnsupportedForBackend(f"{e.name!r} is a number, not a truth value")
        if isinstance(e, ArraySlice):
            raise UnsupportedForBackend("array slices are not supported")
        raise UnsupportedForBackend(f"cannot print {type(e).__name__} as a proposition")

    def _quantified(self, q: QuantifiedExpr) -> str:
        scope: Dict[str, str] = {}
        binders, bounds = [], []
        for p in q.params:
            k = sort_kind(p.type_)
            if k is None:
                raise UnsupportedForBackend(f"quantifier over {p.type_!r} is not supported")
            scope[p.name] = k
            binders.append(f"({p.name} : {k})")
            if isinstance(p.type_, NatType):
                bounds.append(f"(0 <= {p.name})%Z")
        self.bound.append(scope)
        try:
            body = self.prop(q.expr)
        finally:
            self.bound.pop()
        guard = " /\\ ".join(bounds)
        if q.quantifier == "forall":
            if guard:
                body = f"({guard} -> {body})"
            return f"(forall {' '.join(binders)}, {body})"
        if guard:
            body = f"({guard} /\\ {body})"
        return f"(exists {' '.join(binders)}, {body})"


def _conjuncts(e):
    if isinstance(e, BinaryOp) and e.op == "/\\":
        return _conjuncts(e.left) + _conjuncts(e.right)
    return [e]


def _has_integer_atom(printer: CoqPrinter, e) -> bool:
    """Does ``e`` mention a name or array element that is itself integer-valued?

    A bare numeral is polymorphic: ``x = 0`` says nothing about whether ``x`` is whole.
    """
    if isinstance(e, (Variable, Const, VariablePreviousState, ArraySelect)):
        try:
            return printer.kind_of(e) == "Z"
        except UnsupportedForBackend:
            return False
    if isinstance(e, UnaryOp):
        return _has_integer_atom(printer, e.expr)
    if isinstance(e, BinaryOp):
        return _has_integer_atom(printer, e.left) or _has_integer_atom(printer, e.right)
    return False


def _type_defined_integers(env: Env, printer: CoqPrinter, assumptions) -> None:
    """Give an undeclared name the sort ``Z`` when an assumption defines it as an integer.

    The loop laws introduce ``V0``, the variant's starting value, as an undeclared
    name pinned by ``V = V0``. Undeclared names default to ``R`` (as in the Z3
    translator), which for an integer variant forces casts between ``Z`` and
    ``R`` that Coq's linear tactics cannot see through. A name that an assumption
    equates with an integer-valued expression *is* integer-valued, so declaring it
    ``Z`` changes nothing about what is being proved -- only how well it is proved.

    "Integer-valued" needs an integer *name* in the definition: ``x = 0`` is satisfied by a real
    ``x`` just as well, and declaring it ``Z`` would force casts into the real arithmetic around it
    (the square-root derivation's ``x * x <= N`` became ``IZR x * IZR x <= N``, out of ``lra``'s reach).
    """
    for assumption in assumptions:
        for c in _conjuncts(assumption):
            if not (isinstance(c, BinaryOp) and c.op == "="):
                continue
            for named, other in ((c.right, c.left), (c.left, c.right)):
                if (isinstance(named, (Variable, Const)) and named.name not in env.kind
                        and named.name not in env.arrays):
                    try:
                        if printer.kind_of(other) == "Z" and _has_integer_atom(printer, other):
                            env.kind[named.name] = "Z"
                    except UnsupportedForBackend:
                        pass


def obligation_to_coq(obligation, header: str = "") -> Tuple[str, Dict[str, str]]:
    """The body of a ``Goal`` for ``obligation`` and the sorts it quantifies over.

    Returns ``(statement, sorts)`` where ``statement`` is the text after
    ``Goal`` and ``sorts`` maps each free variable to ``Z`` or ``R``.
    """
    env = Env(getattr(obligation, "params", []))
    printer = CoqPrinter(env)
    _type_defined_integers(env, printer, obligation.assumptions)

    hypotheses = [printer.prop(c) for a in obligation.assumptions for c in _conjuncts(a)]
    goal = printer.prop(obligation.goal)

    sorts = dict(printer.used)
    for name in env.nats:
        if name in sorts:
            hypotheses.insert(0, f"(0 <= {name})%Z")

    binders = []
    for kind, shown in (("R", "R"), ("Z", "Z"), ("P", "Prop")):
        names = sorted(n for n, k in sorts.items() if k == kind)
        if names:
            binders.append(f"({' '.join(names)} : {shown})")
    for name, elem in sorted(printer.used_arrays.items()):
        binders.append(f"({name} : Z -> {elem})")

    quant = f"forall {' '.join(binders)}, " if binders else ""
    chain = "".join(f"{h} -> " for h in hypotheses)
    return f"{quant}{chain}{goal}", sorts
