"""Small-scope falsification: evaluate an obligation on *every* small value of its variables.

``plausible`` tests random values, and an obligation whose hypotheses are strong (a loop invariant over the processed part)
is almost never met by random values: it reports nothing, and the step reads as "true but unproved". Most such steps are
false on tiny inputs (o3-mini's loops whose invariant leaves ``i ≤ n`` out fail at ``n = 0, i = 1``). Here every
combination of small values is tried: naturals up to 3, integers -2..2, strings and lists of length up to 2 over the
characters and numbers the obligation itself mentions, and so on. A hypothesis is a ``Decidable`` proposition (``if h : P``),
and the obligation is false on the first combination that meets all hypotheses but not the statement.

    source = falsifier(obligation)          # None: a variable of a type without a small domain, or nothing to enumerate
    lean_reply -> parse(reply_text)         # "a := \"\", i := 1, ..." or None
"""
import itertools
import re
from typing import List, Optional, Tuple

MARK = "SMALLSCOPE:"
LIMIT = 300_000                      # combinations per obligation, at most


def _binders(binders: str) -> Optional[List[Tuple[List[str], str]]]:
    out, depth, start = [], 0, None
    for k, ch in enumerate(binders):
        if ch in "{[" and depth == 0:
            return None
        if ch == "(":
            if depth == 0:
                start = k + 1
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                names, _, typ = binders[start:k].partition(":")
                out.append((names.split(), typ.strip()))
    return out


def _strip(t: str) -> str:
    t = t.strip()
    while t.startswith("(") and t.endswith(")") and _balanced(t[1:-1]):
        t = t[1:-1].strip()
    return t


def _balanced(t: str) -> bool:
    depth = 0
    for ch in t:
        depth += ch == "("
        depth -= ch == ")"
        if depth < 0:
            return False
    return depth == 0


def _split_top(t: str, sep: str) -> List[str]:
    parts, depth, cur = [], 0, ""
    for ch in t:
        depth += ch == "("
        depth -= ch == ")"
        if ch == sep and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    return parts + [cur]


class Domains:
    """Lean list literals of small values per type; ``small`` gives the reduced domains used when the product is too big."""

    def __init__(self, text: str, small: bool):
        chars = sorted(set(re.findall(r"'(\\.|[^'\\])'", text)) - {"\\"})[:3] or ["a"]
        if "a" not in chars and len(chars) < 3:
            chars.append("a")
        ints = {int(n) for n in re.findall(r"(?<![\w.])\d+(?![\w.])", text) if int(n) <= 5}
        self.nat = sorted({0, 1, 2} | ({3} if not small else set()) | (ints if not small else set()))
        # -2 as well as -1: a hypothesis `res ≠ -1` (the "not found" value) leaves -2 as the smallest negative (verina_basic_46)
        self.int = sorted({-1, 0, 1} | ({-2, 2} if not small else set()) | (ints if not small else set()))
        self.chars = chars[:2] if small else chars
        self.small = small

    def of(self, typ: str) -> Optional[List[str]]:
        t = _strip(typ)
        if t in ("Nat", "ℕ"):
            return [str(n) for n in self.nat]
        if t in ("Int", "ℤ"):
            return [f"({n} : Int)" for n in self.int]
        if t == "Bool":
            return ["false", "true"]
        if t == "Char":
            return [self._char(c) for c in self.chars]
        if t == "String":
            return [f"\"{''.join(s)}\"" for n in range(0, 2 if self.small else 3)
                    for s in itertools.product([c.replace('"', '\\"') for c in self.chars], repeat=n)]
        prod = _split_top(t, "×")
        if len(prod) == 2:
            a, b = self.of(prod[0]), self.of(prod[1])
            if a is None or b is None or len(a) * len(b) > 400:
                return None
            return [f"({x}, {y})" for x in a for y in b]
        m = re.fullmatch(r"(List|Option|Array)\s+(.+)", t)
        if m:
            elem = self.of(m.group(2))
            if elem is None:
                return None
            if m.group(1) == "Option":
                return [f"(none : Option ({m.group(2)}))"] + [f"(some {x})" for x in elem]
            elem = elem[:3] if self.small else elem[:4]
            longest = 2 if len(elem) > 2 or self.small else 3
            values = [f"([] : List ({m.group(2)}))"] + ["[" + ", ".join(xs) + "]" for n in range(1, longest + 1)
                                                         for xs in itertools.product(elem, repeat=n)]
            if m.group(1) == "Array":
                values = [f"({v}).toArray" for v in values]
            return values
        return None

    @staticmethod
    def _char(c: str) -> str:
        return "'" + c + "'"


#: ``∀ k, A ∧ k < B → P`` (or ``k < B ∧ A``): the same proposition as ``∀ k, k < B → A → P``, which Lean decides
#: (``Nat.decidableBallLT``); written the first way it has no ``Decidable`` instance and the falsifier gave up (he_024's
#: ``∀ k, d < k ∧ k < n → n % k ≠ 0``)
_BALL = [
    (re.compile(r"∀\s*\(?(\w+)(\s*:\s*(?:ℕ|Nat))?\)?\s*,\s*\(?\s*([^∧→,()]+?)\s*∧\s*\1\s*<\s*([^→()∧]+?)\s*\)?\s*→"),
     r"∀ \1\2, \1 < \4 → \3 →"),
    (re.compile(r"∀\s*\(?(\w+)(\s*:\s*(?:ℕ|Nat))?\)?\s*,\s*\(?\s*\1\s*<\s*([^∧→,()]+?)\s*∧\s*([^→()]+?)\s*\)?\s*→"),
     r"∀ \1\2, \1 < \3 → \4 →"),
]


def _decidable_form(text: str) -> str:
    for pattern, replacement in _BALL:
        text = pattern.sub(replacement, text)
    return text


#: ``∀ d, P d`` (a goal, or a conjunct of one) has no ``Decidable`` instance; ``∀ d, d < 4 → P d`` has one when ``d`` is a
#: natural number, and is implied by it: where the bounded form is false, so is the goal (he_013's invariant
#: ``∀ d, d > 0 → (a % d = 0 ∧ b % d = 0) ↔ ...``, which reads ``(d > 0 → ...) ↔ ...``, fails at ``d = 0``). A binder of
#: another type makes the command fail to elaborate, and the falsifier reports nothing, as before.
BOUND = 4
_FORALL = re.compile(r"∀\s*\(?\s*((?:\w+\s*)+?)\s*(:\s*(?:ℕ|Nat)\s*)?\)?\s*,")
_WEAK = "→↔∨¬∀∃λ"
_SPEC_DEF = re.compile(r"\b(\w+_(?:precond|postcond))\b")


def _beta(t: str) -> str:
    """``(fun (x : A) (y : B) => body) (u) (v)`` as ``body`` with ``x``, ``y`` replaced: the invariant applied to the initial
    state, as the engine states it. Left as it is when a parameter is bound again inside the body."""
    t = _strip(t)
    if not t.startswith("(fun "):
        return t
    depth = 0
    for k, ch in enumerate(t):
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            break
    else:
        return t
    head, _, body = t[5:k].partition("=>")
    # each parameter with its type, which the substituted argument keeps (`([] : List Nat)`)
    params = [(n, typ.strip()) for names, typ in (g.partition(":")[::2] for g in _split_groups(head)) for n in names.split()] \
        if "(" in head else [(n, "") for n in head.split()]
    args, rest, depth, cur = [], t[k + 1:], 0, ""
    for ch in rest:
        depth += ch == "("
        depth -= ch == ")"
        if ch == " " and depth == 0:
            if cur:
                args.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        args.append(cur)
    if not body or len(args) != len(params) or depth != 0:
        return t
    for p, _ in params:
        if re.search(r"(∀|∃|fun|λ)[^,=]*\b" + re.escape(p) + r"(?![\w'])", body):
            return t
    for (p, typ), a in zip(params, args):
        value = f"({_strip(a)} : {typ})" if typ else f"({_strip(a)})"
        body = re.sub(r"(?<![\w.'])" + re.escape(p) + r"(?![\w'])", lambda _: value, body)
    return body.strip()


def _split_groups(head: str) -> List[str]:
    """The contents of the top-level parenthesised groups of ``head``."""
    groups, depth, cur = [], 0, ""
    for ch in head:
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif ch == ")":
            depth -= 1
            if depth == 0:
                groups.append(cur)
                continue
        if depth >= 1:
            cur += ch
    return groups


def _bounded(t: str) -> str:
    t = _strip(t)
    m = _FORALL.match(t)
    if m:
        names, body = m.group(1).split(), t[m.end():].strip()
        # `∀ i, i < n → ...` or `∀ x, x ∈ l → ...` is decidable as it stands (and `x` need not be a number)
        if re.match(r"\(?\s*" + re.escape(names[0]) + r"\s*(<|≤|∈)", body):
            return t
        # the type written out: with `∀ d, d < 4 → ...` instance search runs before the numeral's type is settled
        return f"∀ {' '.join(names)} : ℕ, " + "".join(f"{n} < {BOUND} → " for n in names) + "(" + body + ")"
    parts = _split_top(t, "∧")
    depth, top = 0, ""
    for ch in t:
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            top += ch
    # only a plain conjunction: under `→`, `↔`, `∨` or `¬` the weakening would not be implied by the goal
    if len(parts) > 1 and not any(c in top for c in _WEAK):
        return " ∧ ".join("(" + _bounded(q) + ")" for q in parts)
    return t


def falsifier(binders: str, statement: str) -> Optional[str]:
    """A Lean command printing ``SMALLSCOPE: <assignment>`` for a combination that falsifies the obligation, or
    ``SMALLSCOPE: none``; ``None`` when the obligation's variables have no small domains."""
    binders, statement = _decidable_form(binders), _decidable_form(statement)
    parsed = _binders(binders)
    if not parsed:
        return None
    text = binders + " " + statement          # the domains: from the statement as written, not the bound
    # the invariant applied to the state is reduced only where that lets a `∀` in it be bounded
    reduced = _beta(statement)
    statement = _bounded(reduced) if _bounded(reduced) != _strip(reduced) else _bounded(statement)
    for small in (False, True):
        dom = Domains(text, small)
        data, hyps, total = [], [], 1
        for names, typ in parsed:
            for n in names:
                if n.startswith("h"):
                    hyps.append((n, typ))
                    continue
                values = dom.of(typ)
                if values is None:
                    return None
                data.append((n, typ, values))
                total *= len(values)
        if not data:
            return None
        if total <= LIMIT:
            break
    else:
        return None
    # `h_precond : f_precond a b` (or a postcondition in the statement) is decidable once its definition unfolds
    defs = sorted(set(_SPEC_DEF.findall(binders + " " + statement)) - {n for names, _ in parsed for n in names})
    unfold = (f"set_option allowUnsafeReducibility true in\nattribute [local reducible] {' '.join(defs)} in\n"
              if defs else "")
    lines, ind = [], "    "
    for n, typ, values in data:
        lines.append(f"{ind}for {n} in ([{', '.join(values)}] : List ({typ})) do")
        ind += "  "
    for n, typ in hyps:
        lines.append(f"{ind}if {n} : ({typ}) then")
        ind += "  "
    shown = ' ++ ", " ++ '.join(f'"{n} := " ++ toString (repr {n})' for n, _, _ in data)
    lines.append(f"{ind}if !(decide ({statement})) then")
    lines.append(f"{ind}  return some ({shown})")
    body = "\n".join(lines)
    return (unfold + f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
            f"#eval show IO Unit from do\n"
            f"  let found : Option String := Id.run do\n{body}\n    return none\n"
            f"  IO.println (\"{MARK} \" ++ found.getD \"none\")\n")


def parse(text: str) -> Optional[str]:
    """The falsifying assignment from the command's output, ``None`` when there is none."""
    m = re.search(re.escape(MARK) + r" (.*)", text)
    if not m or m.group(1).strip() == "none":
        return None
    return m.group(1).strip()
