"""A task's definitions (its prelude: precondition, postcondition, helper functions) read into trees, so that the
specification the model sees is written in L_spec like everything else it reads and writes.

``read(prelude)`` splits the prelude into its top-level commands. A ``def``/``abbrev`` becomes a ``Def`` (name,
parameters, result type, and a body or the cases of a definition by cases); anything else (``inductive``,
``structure``, ``instance``, a definition the expression parser does not read) stays a ``Verbatim`` Lean command and
is shown as Lean. ``coverage`` counts both."""
import re
from dataclasses import dataclass, field
from typing import List, Optional, Tuple, Union

from FormalLLM.dsl import lean_syntax, lspec_syntax, ops
from FormalLLM.dsl.ast import Node

#: a line at column 0 starting with one of these opens a new command; any other line continues the current one
_STARTERS = re.compile(r"(@\[|/--|def\b|abbrev\b|theorem\b|lemma\b|instance\b|structure\b|inductive\b|class\b|open\b|"
                       r"namespace\b|end\b|section\b|set_option\b|noncomputable\b|private\b|protected\b|partial\b|"
                       r"#|attribute\b|macro\b|notation\b|infix|variable\b|universe\b|example\b|axiom\b|opaque\b)")
_HEAD = re.compile(r"((?:@\[[^\]]*\]\s*)*)((?:(?:noncomputable|private|protected|partial)\s+)*)(def|abbrev)\s+")


@dataclass
class Def:
    name: str
    params: List[Tuple[str, Optional[Node]]]
    ret: Optional[Node]
    body: Optional[Node] = None                           # `:= body`
    arms: Optional[list] = None                           # `| p => e ...` (a definition by cases)
    attrs: str = ""                                       # `@[reducible, simp]` (kept, not shown)
    keyword: str = "def"
    tail: str = ""                                        # `termination_by ...` / `decreasing_by ...` (kept as Lean)
    source: str = ""
    src: dict = field(default_factory=dict)               # the source text of params / ret / body / arms (for checks)


@dataclass
class Verbatim:
    source: str
    why: str = ""


def commands(prelude: str) -> List[str]:
    """The top-level commands, each with its lines as written (columns matter to the layout rules)."""
    out, cur = [], []
    attached = False              # the last line read is an attribute or a doc comment: it belongs to the next command
    in_doc = False
    for line in prelude.splitlines():
        if line[:1].strip() and _STARTERS.match(line) and not attached and not in_doc:
            if cur:
                out.append("\n".join(cur))
            cur = []
        cur.append(line)
        s = line.strip()
        if not s:
            continue
        if in_doc:
            in_doc = not s.endswith("-/")
            attached = True
        elif s.startswith("/--"):
            in_doc, attached = not s.endswith("-/"), True
        else:
            attached = s.startswith("@[") and s.endswith("]")
    if cur:
        out.append("\n".join(cur))
    return [c.strip("\n") for c in out if c.strip()]


def _at_column(text: str, start: int, end: int) -> str:
    """``text[start:end]`` indented as in the source: Lean's layout rules (where a `let` value ends) read columns, so
    the piece must keep them when it is placed on a line of its own."""
    column = start - (text.rfind("\n", 0, start) + 1)
    return " " * column + text[start:end].rstrip()


def read_def(text: str) -> Def:
    """One ``def``/``abbrev`` command. Raises ``lean_syntax.Unsupported`` when some part is not read."""
    head = _HEAD.match(text)
    if not head:
        raise lean_syntax.Unsupported("not a def")
    # blank the attributes and keyword out (same length, so the columns of the rest stay as written)
    blanked = re.sub(r"[^\n]", " ", text[:head.end()]) + text[head.end():]
    p = lean_syntax._Parser(blanked)

    def here() -> int:                                   # offset of the next token (or the end)
        k = p.k
        while k < len(p.toks) and p.toks[k] == "\n":
            k += 1
        return p.spans[k][0] if k < len(p.toks) else len(text)
    name = p.next()
    src, start = {}, here()
    params, _ = p.binders({":", ":=", "|"})
    src["params"] = text[start:here()].strip()
    ret = None
    if p.peek() == ":":
        p.next()
        start = here()
        ret = p.expr()
        src["ret"] = text[start:here()].strip()
    d = Def(name, params, ret, attrs=head.group(1).strip(), keyword=head.group(3), source=text, src=src)
    if p.peek() == ":=":
        p.next()
        start = here()
        d.body = p.expr()
        src["body"] = _at_column(text, start, here())
    elif p.peek() == "|":
        start = here()
        d.arms = p.arms()
        src["arms"] = _at_column(text, start, here())
    else:
        raise lean_syntax.Unsupported(f"definition {name}: expected ':=' or '|', found {p.peek()!r}")
    rest = p.peek()
    if rest in ("termination_by", "decreasing_by"):
        d.tail = text[here():].strip()
    elif rest is not None:
        raise lean_syntax.Unsupported(f"definition {name}: trailing {rest!r}")
    d.body = d.body and lean_syntax._unparen(d.body)
    d.arms = d.arms and lean_syntax._unparen_any(d.arms)
    d.ret = d.ret and lean_syntax._unparen(d.ret)
    d.params = lean_syntax._unparen_any(d.params)
    return d


def read(prelude: str) -> List[Union[Def, Verbatim]]:
    out: List[Union[Def, Verbatim]] = []
    for cmd in commands(prelude):
        if all(not line.strip() or line.strip().startswith("--") for line in cmd.splitlines()):
            continue                                     # a comment between commands
        if _HEAD.match(cmd):
            try:
                out.append(read_def(cmd))
            except lean_syntax.Unsupported as error:
                out.append(Verbatim(cmd, str(error)))
        else:
            out.append(Verbatim(cmd, "not a definition"))
    return out


# --- printing -----------------------------------------------------------------------------------------------------

def _params_lspec(params) -> str:
    def one(n, t):
        if n == "<pat>":
            return lspec_syntax.show(t)
        if n == "[]":
            return f"[{lspec_syntax.show(t)}]"
        if n.startswith("{"):
            return f"{{{n[1:-1]}: {lspec_syntax.show(t)}}}" if t is not None else n
        return f"{n}: {lspec_syntax.show(t)}" if t is not None else n
    return ", ".join(one(n, t) for n, t in params)


def show_lspec(item: Union[Def, Verbatim]) -> str:
    """The definition as the model reads it; a ``Verbatim`` command is shown as Lean, marked so."""
    if isinstance(item, Verbatim):
        return "-- (Lean)\n" + item.source
    ret = f": {lspec_syntax.show(item.ret)}" if item.ret is not None else ""
    head = f"def {item.name}" + (f"({_params_lspec(item.params)})" if item.params else "") + ret
    if item.body is not None:
        return f"{head} =\n  {lspec_syntax.show(item.body)}"
    arms = "\n".join(f"  | {', '.join(lspec_syntax.show(p) for p in pats)} => {lspec_syntax.show(e)}"
                     for pats, e in item.arms)
    return f"{head}\n{arms}"


def show_lean(item: Union[Def, Verbatim]) -> str:
    """The definition as Lean (attributes and termination clauses as they were)."""
    if isinstance(item, Verbatim):
        return item.source
    params = (" " + lean_syntax._binders(item.params)) if item.params else ""
    ret = f" : {lean_syntax.show(item.ret)}" if item.ret is not None else ""
    head = (item.attrs + "\n" if item.attrs else "") + f"{item.keyword} {item.name}{params}{ret}"
    if item.body is not None:
        text = f"{head} :=\n  {lean_syntax.show(item.body)}"
    else:
        text = head + "\n  " + lean_syntax.show_arms(item.arms, "\n  ")
    return text + ("\n" + item.tail if item.tail else "")


def coverage(prelude: str) -> Tuple[int, int]:
    """(definitions read, top-level commands that need reading: ``open``/``set_option``/... excluded)."""
    items = [i for i in read(prelude)
             if not (isinstance(i, Verbatim) and re.match(r"(open|set_option|namespace|end|section)\b", i.source))]
    return sum(isinstance(i, Def) for i in items), len(items)
