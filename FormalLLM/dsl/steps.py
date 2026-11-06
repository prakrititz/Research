"""A refinement step as the model writes it (L_spec), and the goal it is shown (L_spec).

The model answers with one JSON object whose expressions are L_spec:

    {"law": "term",  "expr": "..."}
    {"law": "cases", "cond": "..."}
    {"law": "bind",  "var": "m", "type": "int", "prop": "..."}
    {"law": "loop",  "state": [["i", "nat", "0"], ["acc", "int", "0"]],
                     "invariant": "...", "guard": "...", "variant": "...", "result": "..."}

and optionally ``"lemmas": [{"name": ..., "statement": <L_spec>, "proof": <Lean, unchanged>}]``.

``to_engine`` turns it into the engine's JSON (the same laws, Lean text); ``from_engine`` is the inverse, used on the
hand-written derivations. A field that cannot be read raises ``StepError`` naming the field, so the model is told which
part of its answer to fix.

The format does not depend on who chose the law: one model that chooses and writes the step, or a selector that names
the law and an applier that writes the rest (``fields_for(law)`` is what the applier must fill)."""
import re
from typing import Dict, List, Optional, Tuple

from FormalLLM.dsl import lean_syntax, lspec_syntax
from FormalLLM.dsl.ast import App, Binder, Let, Match, Name, Node, walk

HOLE = "⟪r⟫"                     # the engine's placeholder for the value being derived (``laws.HOLE``)

#: what each law needs, in the order the applier is asked for it; ``kind``: expr (a value), prop, type, name
FIELDS: Dict[str, List[Tuple[str, str]]] = {
    "term": [("expr", "expr")],
    "cases": [("cond", "prop")],
    "bind": [("var", "name"), ("type", "type"), ("prop", "prop")],
    "loop": [("state", "state"), ("invariant", "prop"), ("guard", "prop"), ("variant", "expr"), ("result", "expr")],
}
_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")


class StepError(ValueError):
    def __init__(self, field: str, message: str):
        super().__init__(f"{field}: {message}")
        self.field = field
        self.message = message


def fields_for(law: str) -> List[Tuple[str, str]]:
    if law not in FIELDS:
        raise StepError("law", f"unknown law {law!r}; the laws are {', '.join(FIELDS)}")
    return FIELDS[law]


# --- one expression ------------------------------------------------------------------------------------------------

def to_lean(text: str, field: str) -> str:
    """L_spec text -> Lean text."""
    if not isinstance(text, str) or not text.strip():
        raise StepError(field, "empty")
    try:
        return lean_syntax.show(lspec_syntax.parse(text))
    except Exception as error:                            # the parser's message, attributed to the field
        raise StepError(field, f"{type(error).__name__}: {error}") from None


def to_lspec(text: str, field: str = "?") -> str:
    """Lean text -> L_spec text."""
    try:
        return lspec_syntax.show(lean_syntax.parse(text))
    except Exception as error:
        raise StepError(field, f"{type(error).__name__}: {error}") from None


def _name(value, field: str) -> str:
    if not isinstance(value, str) or not _NAME.match(value):
        raise StepError(field, f"{value!r} is not a name")
    return value


# --- a step --------------------------------------------------------------------------------------------------------

def to_engine(step: dict) -> dict:
    """The model's L_spec step -> the engine's step (Lean text). Unknown keys are ignored; ``children`` is not touched."""
    if not isinstance(step, dict):
        raise StepError("step", "expected a JSON object")
    law = step.get("law")
    out = {"law": law}
    for field, kind in fields_for(law):
        if field not in step:
            raise StepError(field, "missing")
        value = step[field]
        if kind == "name":
            out[field] = _name(value, field)
        elif kind == "state":
            if not isinstance(value, list) or not value:
                raise StepError("state", 'expected a list of [name, type, initial value], e.g. [["i", "nat", "0"]]')
            out["state"], out["init"] = [], []
            for k, item in enumerate(value):
                if not isinstance(item, (list, tuple)) or len(item) != 3:
                    raise StepError(f"state[{k}]", "expected [name, type, initial value]")
                name, typ, init = item
                out["state"].append([_name(name, f"state[{k}].name"), to_lean(typ, f"state[{k}].type")])
                out["init"].append(to_lean(init, f"state[{k}].initial value"))
        else:
            out[field] = to_lean(value, field)
    lemmas = step.get("lemmas") or []
    if lemmas:
        out["lemmas"] = []
        for k, lemma in enumerate(lemmas):
            if not isinstance(lemma, dict) or not {"name", "statement", "proof"} <= set(lemma):
                raise StepError(f"lemmas[{k}]", "a lemma needs name, statement and proof")
            out["lemmas"].append({"name": _name(lemma["name"], f"lemmas[{k}].name"),
                                  "statement": to_lean(lemma["statement"], f"lemmas[{k}].statement"),
                                  "proof": lemma["proof"]})
    return out


def from_engine(step: dict) -> dict:
    """The engine's step (Lean text) -> L_spec, in the model's format (``children`` dropped)."""
    law = step["law"]
    out = {"law": law}
    for field, kind in fields_for(law):
        if kind == "name":
            out[field] = step[field]
        elif kind == "state":
            out["state"] = [[name, to_lspec(typ, f"state[{k}].type"), to_lspec(init, f"state[{k}].initial value")]
                            for k, ((name, typ), init) in enumerate(zip(step["state"], step["init"]))]
        else:
            out[field] = to_lspec(step[field], field)
    if step.get("lemmas"):
        out["lemmas"] = [{"name": l["name"], "statement": to_lspec(l["statement"], f"lemmas[{k}].statement"),
                          "proof": l["proof"]} for k, l in enumerate(step["lemmas"])]
    return out


# --- trees: substitution and beta reduction (for showing a goal readably) -------------------------------------------

def _map(value, f):
    if isinstance(value, Node):
        return f(value)
    if isinstance(value, list):
        return [_map(v, f) for v in value]
    if isinstance(value, tuple):
        return tuple(_map(v, f) for v in value)
    return value


def _rebuild(node: Node, f) -> Node:
    """``node`` with ``f`` applied to every direct sub-tree."""
    return type(node)(**{k: _map(v, f) for k, v in vars(node).items()})


def _pattern_names(nodes) -> set:
    return {n.id for p in nodes for n in walk(p) if isinstance(n, Name)}


def subst(node: Node, mapping: Dict[str, Node]) -> Node:
    """Replace free occurrences of the names in ``mapping`` (a name a binder rebinds is left alone under it). The
    replacements must not mention names bound inside ``node`` (here they are fresh names and projections of one)."""
    if not mapping:
        return node
    if isinstance(node, Name):
        return mapping.get(node.id, node)
    if isinstance(node, Binder):
        names = {n for n, _ in node.vars if not n.startswith(("<", "[", "{"))}
        names |= _pattern_names([t for n, t in node.vars if n == "<pat>" and t is not None])
        inner = {k: v for k, v in mapping.items() if k not in names}
        return Binder(node.kind, [(n, t if n == "<pat>" or t is None else subst(t, mapping)) for n, t in node.vars],
                      node.bound and (node.bound[0], subst(node.bound[1], mapping)), subst(node.body, inner), node.pattern)
    if isinstance(node, Let):
        bound = {node.name} | {n for n, _ in node.params} | (_pattern_names([node.pattern]) if node.pattern else set())
        inner = {k: v for k, v in mapping.items() if k not in bound}
        value_map = inner if node.rec or node.params else mapping
        return Let(node.name, node.type and subst(node.type, mapping), subst(node.value, value_map),
                   subst(node.body, inner), node.params, node.rec, node.pattern,
                   node.termination and subst(node.termination, inner))
    if isinstance(node, Match):
        arms = []
        for pats, e in node.arms:
            inner = {k: v for k, v in mapping.items() if k not in _pattern_names(pats)}
            arms.append((pats, subst(e, inner)))
        return Match([subst(s, mapping) for s in node.scrutinees], arms)
    return _rebuild(node, lambda n: subst(n, mapping))


def beta(node: Node) -> Node:
    """Apply every ``(lambda x, y: body)(a, b)`` whose parameters are plain names."""
    node = _rebuild(node, beta)
    if isinstance(node, App) and isinstance(node.fn, Binder) and node.fn.kind == "fun" and node.fn.bound is None:
        names = [n for n, _ in node.fn.vars]
        if names and len(node.args) >= len(names) and all(_NAME.match(n) for n in names):
            body = beta(subst(node.fn.body, dict(zip(names, node.args))))
            rest = node.args[len(names):]
            return App(body, rest) if rest else body
    return node


def _replace(node: Node, table: Dict[str, Node]) -> Node:
    key = repr(node)
    if key in table:
        return table[key]
    return _rebuild(node, lambda n: _replace(n, table))


def _projections(r: str, count: int) -> List[Node]:
    """``r.1, r.2.1, ..., r.2...2``: the components of a value of a ``count``-fold product type, as Lean writes them."""
    if count == 1:
        return [Name(r)]
    return [lean_syntax.parse(r + ".2" * k + (".1" if k < count - 1 else "")) for k in range(count)]


# --- the goal --------------------------------------------------------------------------------------------------------

def result_name(goal) -> str:
    """What the value being derived is called in the goal shown to the model (not a name the goal already uses)."""
    taken = {n for n, _ in goal.ctx} | {n for n, _ in goal.hyps} | set(re.findall(r"[A-Za-z_][\w']*", goal.post))
    name = "result"
    while name in taken:
        name += "_"
    return name


def goal_to_lspec(goal, state: Optional[List[str]] = None) -> dict:
    """The goal in L_spec: what is known (inputs and their types, assumptions), what to find (its type) and the
    property it must have.

    ``state``: the goal is a loop's body (find the next state), over these state variables. The next state is then
    shown as named components (``i_next, acc_next``) and the property with the invariant and variant applied to them,
    instead of ``(lambda i, acc: ...)(result.1, result.2)``."""
    r = result_name(goal)
    shown = {"inputs": [[n, to_lspec(t, f"input {n}")] for n, t in goal.ctx],
             "assumptions": [[n, to_lspec(p, f"assumption {n}")] for n, p in goal.hyps],
             "find": [r, to_lspec(goal.ret, "result type")],
             "such_that": to_lspec(goal.post.replace(HOLE, r), "property")}
    if state:
        taken = {n for n, _ in goal.ctx} | {n for n, _ in goal.hyps} | set(re.findall(r"[A-Za-z_][\w']*", goal.post))
        names = []
        for n in state:
            name = f"{n}_next"
            while name in taken or name in names:
                name += "_"
            names.append(name)
        tree = beta(lean_syntax.parse(goal.post.replace(HOLE, r)))
        tree = _replace(tree, {repr(p): Name(n) for p, n in zip(_projections(r, len(names)), names)})
        if not any(isinstance(n, Name) and n.id == r for n in walk(tree)):       # every use of r was a component
            shown["find"][0] = "(" + ", ".join(names) + ")" if len(names) > 1 else names[0]
            shown["such_that"] = lspec_syntax.show(tree)
            shown["next"], shown["as"] = names, r
    return shown


def goal_from_lspec(shown: dict) -> Tuple[str, str]:
    """The Lean statement the L_spec goal stands for: ``(binders, ∃ r : T, property)`` (for checking ``goal_to_lspec``;
    a loop body's goal, shown with named components, stands for the statement up to beta reduction)."""
    binders = " ".join([f"({n} : {to_lean(t, n)})" for n, t in shown["inputs"]] +
                       [f"({n} : {to_lean(p, n)})" for n, p in shown["assumptions"]])
    typ = to_lean(shown["find"][1], "result type")
    if "next" in shown:
        r = shown["as"]
        try:
            tree = lspec_syntax.parse(shown["such_that"])
        except Exception as error:
            raise StepError("property", f"{type(error).__name__}: {error}") from None
        tree = subst(tree, dict(zip(shown["next"], _projections(r, len(shown["next"])))))
        return binders, f"∃ {r} : {typ}, {lean_syntax.show(tree)}"
    return binders, f"∃ {shown['find'][0]} : {typ}, {to_lean(shown['such_that'], 'property')}"


def goal_text(shown: dict) -> str:
    """The goal as the model reads it."""
    lines = ["Inputs:"] + [f"  {n}: {t}" for n, t in shown["inputs"]]
    if shown["assumptions"]:
        lines += ["Assumptions:"] + [f"  {n}: {p}" for n, p in shown["assumptions"]]
    r, typ = shown["find"]
    lines += [f"Find {r}: {typ}", f"such that {shown['such_that']}"]
    return "\n".join(lines)
