"""Small-scope falsification: evaluate an obligation on *every* small value of its variables.

``plausible`` tests random values, and an obligation whose hypotheses are strong (a loop invariant over the processed part)
is almost never met by random values: it reports nothing, and the step reads as "true but unproved". Most such steps are
false on tiny inputs (o3-mini's loops whose invariant leaves ``i ≤ n`` out fail at ``n = 0, i = 1``). Here every
combination of small values is tried: naturals up to 3, integers -1..2, strings and lists of length up to 2 over the
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
        self.int = sorted({-1, 0, 1} | ({2} if not small else set()) | (ints if not small else set()))
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


def falsifier(binders: str, statement: str) -> Optional[str]:
    """A Lean command printing ``SMALLSCOPE: <assignment>`` for a combination that falsifies the obligation, or
    ``SMALLSCOPE: none``; ``None`` when the obligation's variables have no small domains."""
    parsed = _binders(binders)
    if not parsed:
        return None
    text = binders + " " + statement
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
    return (f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
            f"#eval show IO Unit from do\n"
            f"  let found : Option String := Id.run do\n{body}\n    return none\n"
            f"  IO.println (\"{MARK} \" ++ found.getD \"none\")\n")


def parse(text: str) -> Optional[str]:
    """The falsifying assignment from the command's output, ``None`` when there is none."""
    m = re.search(re.escape(MARK) + r" (.*)", text)
    if not m or m.group(1).strip() == "none":
        return None
    return m.group(1).strip()
