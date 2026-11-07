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
import json
import re
from typing import Dict, List, Optional, Tuple

from FormalLLM.dsl import lean_syntax, lspec_syntax
from FormalLLM.dsl.ast import App, BinOp, Binder, Let, Match, Name, Node, walk

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

def _text(value):
    """A JSON value where L_spec text was expected (models write `false`, `0`, `[]` unquoted): its L_spec text."""
    if isinstance(value, bool):
        return "True" if value else "False"
    if isinstance(value, (int, float)):
        return repr(value)
    if isinstance(value, list):
        items = [_text(v) for v in value]
        return "[" + ", ".join(items) + "]" if all(isinstance(i, str) for i in items) else value
    return value


def to_lean(text: str, field: str, scope=()) -> str:
    """L_spec text -> Lean text; ``scope``: the variables in scope (a name among them is that variable)."""
    text = _text(text)
    if not isinstance(text, str) or not text.strip():
        raise StepError(field, 'empty: an expression is needed (the empty string is `""`, written "\\"\\"" in JSON; '
                               'the empty list is "[]")')
    try:
        return lean_syntax.show(lspec_syntax.parse(text, scope))
    except Exception as error:                            # the parser's message, attributed to the field
        raise StepError(field, f"{type(error).__name__}: {error}") from None


def to_lspec(text: str, field: str = "?", scope=()) -> str:
    """Lean text -> L_spec text, to be read back with ``to_lean(..., scope)``."""
    try:
        return lspec_syntax.show_in(lean_syntax.parse(text), scope)
    except Exception as error:
        raise StepError(field, f"{type(error).__name__}: {error}") from None


def _name(value, field: str) -> str:
    if not isinstance(value, str) or not _NAME.match(value):
        raise StepError(field, f"{value!r} is not a name")
    return value


# --- a step --------------------------------------------------------------------------------------------------------

def to_engine(step: dict, scope=()) -> dict:
    """The model's L_spec step -> the engine's step (Lean text). ``scope``: the goal's variables (and assumption names);
    a loop's state and a bind's variable are added where they are in scope. Unknown keys are ignored."""
    if not isinstance(step, dict):
        raise StepError("step", "expected a JSON object")
    law = step.get("law")
    out = {"law": law}
    if law == "bind" and "prop" not in step and "value" in step and isinstance(step.get("var"), str):
        step = {**step, "prop": f"{step['var']} == ({_text(step['value'])})", "_value": True}          # bind to a known value
    inner = set(scope)
    if law == "loop" and isinstance(step.get("state"), list):
        inner |= {item[0] for item in step["state"] if isinstance(item, (list, tuple)) and item and isinstance(item[0], str)}
    if law == "bind" and isinstance(step.get("var"), str):
        inner.add(step["var"])
    for field, kind in fields_for(law):
        if field not in step:
            raise StepError(field, f"missing: a `{law}` step has the fields "
                                   + ", ".join(f"`{f}`" for f, _ in fields_for(law)))
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
                out["state"].append([_name(name, f"state[{k}].name"), to_lean(typ, f"state[{k}].type", scope)])
                out["init"].append(to_lean(init, f"state[{k}].initial value", scope))
        elif field == "type":
            out[field] = to_lean(value, field, scope)
        else:
            out[field] = to_lean(value, field, inner)
    _shadow(out, scope, step)
    lemmas = step.get("lemmas") or []
    if lemmas:
        out["lemmas"] = []
        for k, lemma in enumerate(lemmas):
            if not isinstance(lemma, dict) or not {"name", "statement", "proof"} <= set(lemma):
                raise StepError(f"lemmas[{k}]", "a lemma needs name, statement and proof")
            out["lemmas"].append({"name": _name(lemma["name"], f"lemmas[{k}].name"),
                                  "statement": to_lean(lemma["statement"], f"lemmas[{k}].statement", scope),
                                  "proof": lemma["proof"]})
    return out


def _shadow(out: dict, scope, step: dict) -> None:
    """A loop's state variable or a bind's variable named like a variable of the goal shadows it, as reassigning a
    variable does in Python: it is renamed (``found`` -> ``found2``) where the new variable is in scope (invariant,
    guard, variant, result; a bind's property), and the old name keeps meaning the goal's variable elsewhere (initial
    values)."""
    if out.get("law") == "loop":
        names = [item[0] for item in out["state"]]
    elif out.get("law") == "bind":
        names = [out["var"]]
    else:
        return
    clash = [n for n in names if n in set(scope)]
    if not clash:
        return
    taken = set(scope) | set(re.findall(r"[A-Za-z_][\w']*", json.dumps(step, ensure_ascii=False)))
    renames = {}
    for name in clash:
        k = 2
        while f"{name}{k}" in taken:
            k += 1
        renames[name] = f"{name}{k}"
        taken.add(renames[name])
    mapping = {old: Name(new) for old, new in renames.items()}
    if out["law"] == "loop":
        out["state"] = [[renames.get(n, n), t] for n, t in out["state"]]
        fields = ("invariant", "guard", "variant", "result")
    else:
        out["var"] = renames[out["var"]]
        fields = ("prop",)
    for field in fields:
        tree = lean_syntax.parse(out[field])
        if step.get("_value"):                             # `x = value`: the value is computed before x is bound
            tree = BinOp(tree.op, mapping[tree.left.id], tree.right)
        else:
            tree = subst(tree, mapping)
        out[field] = lean_syntax.show(tree)


def from_engine(step: dict, scope=()) -> dict:
    """The engine's step (Lean text) -> L_spec, in the model's format (``children`` dropped); ``scope`` as for
    ``to_engine``, which reads the result back."""
    law = step["law"]
    out = {"law": law}
    inner = set(scope)
    if law == "loop":
        inner |= {name for name, _ in step["state"]}
    if law == "bind":
        inner.add(step["var"])
    for field, kind in fields_for(law):
        if kind == "name":
            out[field] = step[field]
        elif kind == "state":
            out["state"] = [[name, to_lspec(typ, f"state[{k}].type", scope),
                             to_lspec(init, f"state[{k}].initial value", scope)]
                            for k, ((name, typ), init) in enumerate(zip(step["state"], step["init"]))]
        else:
            out[field] = to_lspec(step[field], field, scope if field == "type" else inner)
    if step.get("lemmas"):
        out["lemmas"] = [{"name": l["name"], "statement": to_lspec(l["statement"], f"lemmas[{k}].statement", scope),
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
    scope = [n for n, _ in goal.ctx] + [n for n, _ in goal.hyps]
    shown = {"inputs": [[n, to_lspec(t, f"input {n}", scope)] for n, t in goal.ctx],
             "assumptions": [[n, to_lspec(p, f"assumption {n}", scope)] for n, p in goal.hyps],
             "find": [r, to_lspec(goal.ret, "result type", scope)],
             "such_that": to_lspec(goal.post.replace(HOLE, r), "property", scope + [r])}
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
            shown["such_that"] = lspec_syntax.show_in(tree, scope + names + [r])
            shown["next"], shown["as"] = names, r
    return shown


def goal_from_lspec(shown: dict) -> Tuple[str, str]:
    """The Lean statement the L_spec goal stands for: ``(binders, ∃ r : T, property)`` (for checking ``goal_to_lspec``;
    a loop body's goal, shown with named components, stands for the statement up to beta reduction)."""
    scope = [n for n, _ in shown["inputs"]] + [n for n, _ in shown["assumptions"]]
    binders = " ".join([f"({n} : {to_lean(t, n, scope)})" for n, t in shown["inputs"]] +
                       [f"({n} : {to_lean(p, n, scope)})" for n, p in shown["assumptions"]])
    typ = to_lean(shown["find"][1], "result type", scope)
    if "next" in shown:
        r = shown["as"]
        try:
            tree = lspec_syntax.parse(shown["such_that"], scope + list(shown["next"]) + [shown["as"]])
        except Exception as error:
            raise StepError("property", f"{type(error).__name__}: {error}") from None
        tree = subst(tree, dict(zip(shown["next"], _projections(r, len(shown["next"])))))
        return binders, f"∃ {r} : {typ}, {lean_syntax.show(tree)}"
    return binders, f"∃ {shown['find'][0]} : {typ}, {to_lean(shown['such_that'], 'property', scope + [shown['find'][0]])}"


def goal_text(shown: dict) -> str:
    """The goal as the model reads it."""
    lines = ["Inputs:"] + [f"  {n}: {t}" for n, t in shown["inputs"]]
    if shown["assumptions"]:
        lines += ["Assumptions:"] + [f"  {n}: {p}" for n, p in shown["assumptions"]]
    r, typ = shown["find"]
    lines += [f"Find {r}: {typ}", f"such that {shown['such_that']}"]
    return "\n".join(lines)
