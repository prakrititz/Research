"""Conversions the translator inserts when Lean rejects a step only because Lean distinguishes what Python does not.

L_spec reads like Python, where there is no character type, a string is a sequence of characters, a boolean counts
as 0 or 1, and calling a conversion on a value that already has the target type does nothing. Lean distinguishes
all of these. So a step that is well typed in Python's sense can still be rejected by Lean. When Lean's error names
the term and the two types, and one conversion settles it, the conversion is inserted and the step is checked again.

The repairs are fixed; none of them depends on the task:

* ``list[char]`` where a ``str`` is expected: ``String.mk(x)``; the other way round: ``list(x)``
* a ``char`` where a ``str`` is expected: ``"c"`` for a literal, otherwise ``String.singleton(c)``; a one-character
  ``str`` literal where a ``char`` is expected: ``'c'``; ``[]`` where a ``str`` is expected: ``""``
* a ``bool`` or a statement used as a number: ``(1 if p else 0)``, as Python's ``True + 1 == 2``
* converting to the type the value already has (``to_nat`` of a ``nat``, ``list`` of a list): dropped
* a ``bind`` whose ``prop`` is a value, not a statement, and does not mention the variable: ``var == (value)``

A repair only runs when Lean rejected the step, and its result is checked by Lean again, so a step that type-checks
as written is never changed. The model is told what was read differently (``describe``)."""
import re
from collections import Counter
from typing import Callable, Dict, List, Optional, Tuple

from FormalLLM.dsl import lean_syntax
from FormalLLM.dsl.ast import App, Binder, BinOp, Char, Dot, If, ListLit, Name, Node, Num, Str, UnOp, walk

#: the fields of an engine step that hold Lean expressions (``init`` is a list of them)
EXPR_FIELDS = ("expr", "cond", "prop", "invariant", "guard", "variant", "result", "init")

_TYPES = {"ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat", "ℝ": "Real"}
_NUMBER = {"Nat", "Int", "Rat", "Real", "Float"}
_BOOLISH = {"Bool", "Prop"}
_PROP_OPS = {"=", "≠", "<", ">", "≤", "≥", "∈", "∉", "∧", "∨", "→", "↔", "==", "!=", "∣"}

_MISMATCH = re.compile(r"(?:The argument|Type mismatch)\s+(?P<term>.+?)\s+has type\s+(?P<have>.+?)\s+"
                       r"(?:of sort .+?\s+)?but is expected to have type\s+(?P<want>.+?)"
                       r"(?:\s+of sort .+?)?(?:\s+in the application|\s*$|\s+Note:|\s+Hint:)", re.S)
_FIELD = re.compile(r"does not contain `(?P<type>[\w.]+)\.(?P<field>\w+)`, so it is not possible to project the field "
                    r"`\w+` from an expression\s+(?P<term>.+?)\s+of type `(?P<have>[^`]+)`", re.S)
_SYNTH = re.compile(r"failed to synthesize instance of type class\s+H(?:Add|Sub|Mul|Div|Mod)\s+(\S+)\s+(\S+)")

#: a conversion whose target is the type its argument already has, by that type: the field it is called by
_SELF_CONVERSIONS = {"Nat": {"toNat"}, "Int": {"toInt"}, "List": {"toList"}, "String": {"toString"},
                     "Array": {"toArray"}, "Rat": {"toRat"}}


def _type(text: str) -> str:
    text = re.sub(r"\s*:\s*(Type|Sort)\b.*$", "", " ".join(text.split()))         # `ℕ : Type`
    for k, v in _TYPES.items():
        text = re.sub(rf"(?<!\w){k}(?!\w)", v, text)
    return text.strip("`")


def _strip(node: Node) -> Node:
    """The term without the coercions Lean prints and the step did not write (``decide``, ``↑``)."""
    while True:
        if isinstance(node, App) and isinstance(node.fn, Name) and node.fn.id == "decide" and len(node.args) == 1:
            node = node.args[0]
        elif isinstance(node, UnOp) and node.op == "↑":
            node = node.arg
        else:
            return node


def _leaves(node: Node) -> Counter:
    """The names, literals and fields of a term, without namespaces or inserted coercions: the same for a term as
    Lean prints it (``List.filter p l``) and as the step wrote it (``l.filter p``)."""
    out = Counter()
    for n in walk(node):
        if isinstance(n, Name) and n.id != "decide":
            out["n:" + n.id.split(".")[-1]] += 1
        elif isinstance(n, (Num, Str, Char)):
            out[f"{type(n).__name__}:{n.text}"] += 1
        elif isinstance(n, Dot):
            out["n:" + n.field] += 1
        elif isinstance(n, ListLit) and not n.items:
            out["[]"] += 1
    return out


def _rebuild(node: Node, f: Callable[[Node], Node]) -> Node:
    def m(v):
        if isinstance(v, Node):
            return f(v)
        if isinstance(v, list):
            return [m(x) for x in v]
        if isinstance(v, tuple):
            return tuple(m(x) for x in v)
        return v
    return type(node)(**{k: m(v) for k, v in vars(node).items()})


class _Matcher:
    """Replaces the largest sub-terms whose leaves are ``key`` (outermost first), counting them across the fields of a
    step; ``only``: replace just the occurrence with that number (the others keep their type)."""

    def __init__(self, key: Counter, new: Callable[[Node], Node], only: Optional[int] = None):
        self.key, self.new, self.only, self.seen = key, new, only, 0

    def __call__(self, node: Node) -> Tuple[Node, int]:
        replaced = 0

        def go(n: Node) -> Node:
            nonlocal replaced
            if _leaves(n) == self.key:
                k, self.seen = self.seen, self.seen + 1
                if self.only is None or self.only == k:
                    replaced += 1
                    return self.new(n)
                return n
            return _rebuild(n, go)
        return go(node), replaced


def _boolish(node: Node) -> bool:
    node = _strip(node)
    return ((isinstance(node, BinOp) and node.op in _PROP_OPS) or (isinstance(node, UnOp) and node.op == "¬")
            or (isinstance(node, Binder) and node.kind in ("∀", "∃"))
            or (isinstance(node, Name) and node.id in ("true", "false", "True", "False")))


def _as_number(node: Node) -> Node:
    return If(node, Num("1"), Num("0"))


def _conversion(have: str, want: str, term: Node) -> Optional[Callable[[Node], Node]]:
    """The conversion from ``have`` to ``want`` that Python would not need, or None."""
    if have == "List Char" and want == "String":
        return lambda n: App(Name("String.mk"), [n])
    if have == "String" and want == "List Char":
        return lambda n: Dot(n, "toList")
    if have == "Char" and want == "String":
        return lambda n: Str(n.text) if isinstance(n, Char) else App(Name("String.singleton"), [n])
    if have == "String" and want == "Char" and isinstance(term, Str) and len(term.text) == 1:
        return lambda n: Char(n.text) if isinstance(n, Str) else n
    if have.startswith("List") and want == "String" and isinstance(term, ListLit) and not term.items:
        return lambda n: Str("")
    if have in _BOOLISH and want in _NUMBER:
        return _as_number
    return None


def _apply(step: dict, change: Callable[[Node], Tuple[Node, int]]) -> Tuple[dict, List[str]]:
    """``change`` applied to every expression field of ``step``: the new step and the fields that changed."""
    out, changed = dict(step), []

    def one(text: str) -> Tuple[str, bool]:
        try:
            tree = lean_syntax.parse(text)
        except Exception:
            return text, False
        new, count = change(tree)
        return (lean_syntax.show(new), True) if count else (text, False)

    for field in EXPR_FIELDS:
        if field not in step:
            continue
        if field == "init":
            values = [one(v) for v in step["init"]]
            if any(c for _, c in values):
                out["init"] = [v for v, _ in values]
                changed.append("init")
        elif isinstance(step[field], str):
            out[field], c = one(step[field])
            if c:
                changed.append(field)
    return out, changed


def repairs(step: dict, error: str) -> List[Tuple[dict, str]]:
    """The repaired steps Lean's ``error`` suggests for the engine step ``step`` (Lean text), each with what was
    changed (one line); empty when no repair applies. Each candidate is to be checked again."""
    found: List[Tuple[dict, str]] = []
    if step.get("law") == "bind" and re.search(r"expected to have type\s+Prop|H\w+ \S+ \S+ Prop|\bProp of sort", error):
        try:
            tree = lean_syntax.parse(step["prop"])
            mentions = any(isinstance(n, Name) and n.id == step["var"] for n in walk(tree))
        except Exception:
            mentions = True
        if not mentions and not _boolish(tree):
            found.append(({**step, "prop": lean_syntax.show(BinOp("=", Name(step["var"]), tree))},
                          "the bind's prop is a value, read as `var == (value)`"))
    m = _MISMATCH.search(error)
    if m:
        have, want = _type(m["have"]), _type(m["want"])
        try:
            term = _strip(lean_syntax.parse(" ".join(m["term"].split())))
        except Exception:
            term = None
        convert = _conversion(have, want, term) if term is not None else None
        if convert:
            key = _leaves(term)
            every = _Matcher(key, convert)
            new, changed = _apply(step, every)
            if changed:
                found.append((new, f"a {have} where a {want} is expected: converted"))
            if every.seen > 1:                             # or only one of them (the others may need their type)
                for k in range(min(every.seen, 6)):
                    new, changed = _apply(step, _Matcher(key, convert, only=k))
                    if changed:
                        found.append((new, f"a {have} where a {want} is expected: converted (one occurrence)"))
    m = _FIELD.search(error)
    if m and m["field"] in _SELF_CONVERSIONS.get(_type(m["have"]).split()[0], ()):
        field = m["field"]

        def drop(t: Node) -> Tuple[Node, int]:
            count = 0

            def go(n: Node) -> Node:
                nonlocal count
                if isinstance(n, Dot) and n.field == field:
                    try:
                        same = _leaves(n.obj) == _leaves(_strip(lean_syntax.parse(" ".join(m["term"].split()))))
                    except Exception:
                        same = False
                    if same:
                        count += 1
                        return go(n.obj)
                return _rebuild(n, go)
            return go(t), count
        new, changed = _apply(step, drop)
        if changed:
            found.append((new, f"`{field}` of a value that already has that type: dropped"))
    m = _SYNTH.search(error)
    if m and ({_type(m[1]), _type(m[2])} & _BOOLISH) and ({_type(m[1]), _type(m[2])} & _NUMBER):
        def wrap(t: Node) -> Tuple[Node, int]:
            count = 0

            def go(n: Node) -> Node:
                nonlocal count
                n = _rebuild(n, go)
                if isinstance(n, BinOp) and n.op in ("+", "-", "*", "/", "%"):
                    parts = []
                    for side in (n.left, n.right):
                        if _boolish(side):
                            count += 1
                            side = _as_number(side)
                        parts.append(side)
                    return BinOp(n.op, *parts)
                return n
            return go(t), count
        new, changed = _apply(step, wrap)
        if changed:
            found.append((new, "a statement used as a number: read as `(1 if p else 0)`"))
    return found


def describe(before: dict, after: dict, to_lspec: Callable[[str], str]) -> str:
    """What the translator read differently, in L_spec, for the model."""
    lines = []
    for field in EXPR_FIELDS:
        if before.get(field) != after.get(field):
            if field == "init":
                for k, (a, b) in enumerate(zip(before["init"], after["init"])):
                    if a != b:
                        lines.append(f"  initial value {k + 1}: {to_lspec(b)}")
            else:
                lines.append(f"  {field}: {to_lspec(after[field])}")
    return "\n".join(lines)


# --- the written text, before translation ------------------------------------------------------------------------------

def _closing_typo(text: str) -> Optional[str]:
    """``}`` typed for ``)``: only when the text has no ``{`` at all (so a ``}`` closes nothing else) and the counts
    say each ``}`` closes an open ``(`` (he_070: ``range(n).map(lambda k: ... }``)."""
    if "}" not in text or "{" in text or text.count("(") != text.count(")") + text.count("}"):
        return None
    return text.replace("}", ")")


def text_repairs(written: dict) -> Optional[Tuple[dict, str]]:
    """A step whose L_spec text does not parse, with an unambiguous typo corrected (the step is then translated and
    checked as usual); ``None`` if there is none."""
    fixed, changed = dict(written), []
    for field in EXPR_FIELDS:
        value = written.get(field)
        if isinstance(value, str) and _closing_typo(value) is not None:
            fixed[field] = _closing_typo(value)
            changed.append(field)
    if isinstance(written.get("state"), list):
        state = []
        for entry in written["state"]:
            if isinstance(entry, list) and len(entry) == 3 and isinstance(entry[2], str) and _closing_typo(entry[2]):
                entry = [entry[0], entry[1], _closing_typo(entry[2])]
                changed.append(f"initial value of {entry[0]}")
            state.append(entry)
        fixed["state"] = state
    if not changed:
        return None
    return fixed, "`}` read as `)` in " + ", ".join(changed)
