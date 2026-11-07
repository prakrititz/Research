"""L_spec, the language the model writes: a printer (``ast`` -> L_spec text) and a parser (L_spec text -> ``ast``).

Python's surface on Lean's meaning. Operators group exactly as in Lean (the same precedence table), only their spelling
changes (``ops.BINOPS``); names come from the registry (``ops.py``). The constructs:

    lambda acc, (s, e): acc + (e - s)          forall i < len(l): l[i] >= 0          exists x in l: x % 2 == 0
    a if c else b                               let m = len(l); m * 2                  match v with | some x => x | none => 0
    l[i]  (l[i]! in Lean)   l[i]?   l[:k] (take)   l[k:] (drop)   len(l)   sorted(l, c)   x.map(f)   (e as int)
    list[int]   tuple[nat, bool]   abs(x)   floor(x)   bool(p) (decide; `bool` alone is the type)   True / False
    `name` (a name L_spec reserves)
"""
import re
from typing import List, Optional

from FormalLLM.dsl import ops
from FormalLLM.dsl.ast import (Abs, Anon, App, Ascribe, Binder, BinOp, Char, Dot, If, Index, Let, ListLit, Match,
                               Name, Node, Num, Str, Tuple_, UnOp)
from FormalLLM.dsl.lean_syntax import INFIX, PREFIX, Unsupported, _dotted

ABS_FUNCS = {"|": "abs", "⌊": "floor", "⌈": "ceil", "⌊₊": "floor_nat", "⌈₊": "ceil_nat"}
ABS_INV = {v: k for k, v in ABS_FUNCS.items()}
TYPE_CTORS = {"List", "Array", "Option"}                  # `list[int]` is `List Int`
BOUNDS = {"∈": "in", "∉": "not in", "<": "<", "≤": "<=", ">": ">", "≥": ">="}
BOUNDS_INV = {v: k for k, v in BOUNDS.items()}
#: Python's function form, read as the method (never printed): `map(f, l)` is `l.map(f)`, `filter(p, l)` is `l.filter(p)`
PY_FUNCS = {"map", "filter"}
#: String methods whose arguments are strings in Lean: a one-character literal there is a string, as in Python
STRING_ARGS = {"splitOn", "startsWith", "endsWith", "intercalate"}
#: comparisons that chain as in Python (`a < b <= c` is `a < b and b <= c`)
CHAIN = {"=", "≠", "<", ">", "≤", "≥"}

# --- printing -----------------------------------------------------------------------------------------------------

_ATOMS = (Name, Num, Char, Str, ListLit, Tuple_, Anon, Abs, App, Dot, Index, Ascribe)


def _name(lean: str) -> str:
    if lean in _SCOPE:                                     # a variable where the text is read: no escape needed
        return lean
    if lean in ops.NAMES:                                  # Lean's name when the L_spec one is a variable in scope
        return lean if ops.NAMES[lean] in _SCOPE else ops.NAMES[lean]
    if lean in ops.RESERVED:
        return f"`{lean}`"
    return lean


def _arg(node: Node) -> str:
    text = show(node)
    return text if isinstance(node, _ATOMS) else f"({text})"


_ATOM_OPS = ("×", "<|", "$")                               # printed as `tuple[...]` / a call: never need parentheses


def _operand(child: Node, op: str, side: str) -> str:
    """An operand of ``op``: an operator expression is parenthesised only when Lean's precedences would group it
    differently without (the parser reads with the same table, so the text reads back to the same tree)."""
    if isinstance(child, BinOp) and child.op in _ATOM_OPS:
        return show(child)
    if isinstance(child, BinOp) and child.op in CHAIN and op in CHAIN:          # it would read as a chain
        return f"({show(child)})"
    if isinstance(child, BinOp) and child.op in INFIX and op in INFIX:
        prec, right_assoc = INFIX[op]
        inner, _ = INFIX[child.op]
        if inner > prec or inner == prec and (side == "left") != right_assoc:
            return show(child)
        return f"({show(child)})"
    return _arg(child)


def _low(node: Node) -> str:
    """A part that would swallow what follows (`lambda`, a conditional, `let`, `match`) is parenthesised."""
    text = show(node)
    return f"({text})" if isinstance(node, (Binder, If, Let, Match)) else text


def _method(field: str) -> str:
    if field in ops.METHODS:
        return ops.METHODS[field]
    if field in ops.METHODS_INV or ops.METHOD_FUNCS_INV.get(field, field) != field or field in ops.METHOD_ALIASES:
        return f"`{field}`"                                # a Lean field the reader would take for another one
    return field


def _product(node: Node) -> List[Node]:
    out = []
    while isinstance(node, BinOp) and node.op == "×":
        out.append(node.left)
        node = node.right
    return out + [node]


def show(node: Node) -> str:
    if isinstance(node, Name):
        return _name(node.id)
    if isinstance(node, Num):
        return node.text
    if isinstance(node, Char):
        return f"'{node.text}'"
    if isinstance(node, Str):
        return f'"{node.text}"'
    if isinstance(node, App):
        args = [show(a) for a in node.args]
        fn = node.fn
        if isinstance(fn, Dot):
            if fn.field in ops.METHOD_FUNCS and ops.METHOD_FUNCS[fn.field] not in _SCOPE:
                return f"{ops.METHOD_FUNCS[fn.field]}({', '.join([show(fn.obj)] + args)})"
            if fn.field in ("take", "drop") and len(args) == 1:
                return f"{_arg(fn.obj)}[{':' + args[0] if fn.field == 'take' else args[0] + ':'}]"
            return f"{_arg(fn.obj)}.{_method(fn.field)}({', '.join(args)})"
        if isinstance(fn, Name) and fn.id in TYPE_CTORS and len(args) == 1:
            return f"{_name(fn.id)}[{args[0]}]"
        if isinstance(fn, Name) and fn.id in ops.CALL_NAMES and ops.CALL_NAMES[fn.id] not in _SCOPE:          # `decide p` is `bool(p)`
            return f"{ops.CALL_NAMES[fn.id]}({', '.join(args)})"
        head = _name(fn.id) if isinstance(fn, Name) else f"({show(fn)})"
        return f"{head}({', '.join(args)})"
    if isinstance(node, Dot):
        if (node.field == "get!" and isinstance(node.obj, Dot) and node.obj.field in ("max?", "min?")
                and node.obj.field[:3] not in _SCOPE):                       # `l.max?.get!` is `max(l)`
            return f"{node.obj.field[:3]}({show(node.obj.obj)})"
        if node.field in ops.METHOD_FUNCS and ops.METHOD_FUNCS[node.field] not in _SCOPE:
            return f"{ops.METHOD_FUNCS[node.field]}({show(node.obj)})"
        return f"{_arg(node.obj)}.{_method(node.field)}"
    if isinstance(node, Index):
        idx = show(node.idx)
        return {"!": f"{_arg(node.obj)}[{idx}]", "?": f"{_arg(node.obj)}[{idx}]?", "": f"{_arg(node.obj)}[[{idx}]]"}[node.kind]
    if isinstance(node, BinOp):
        if node.op == "×":
            return "tuple[" + ", ".join(show(p) for p in _product(node)) + "]"
        if node.op in ("<|", "$"):
            return show(App(node.left, [node.right]))
        return f"{_operand(node.left, node.op, 'left')} {ops.BINOPS.get(node.op, node.op)} {_operand(node.right, node.op, 'right')}"
    if isinstance(node, UnOp):
        op = ops.UNOPS[node.op]
        return f"{op}{' ' if op.isalpha() else ''}{_arg(node.arg)}"
    if isinstance(node, Binder):
        head = _binders(node.vars)
        if node.bound:
            head += f" {BOUNDS[node.bound[0]]} {_arg(node.bound[1])}"
        kind = {"fun": "lambda", "∀": "forall", "∃": "exists"}[node.kind]
        return f"{kind} {head}: {show(node.body)}"
    if isinstance(node, If):
        cond = show(node.cond) if not isinstance(node.cond, (Binder, If, Let, Match)) else f"({show(node.cond)})"
        hyp = f"{node.hyp} := " if node.hyp else ""
        return f"{_low(node.then)} if {hyp}{cond} else {show(node.other)}"
    if isinstance(node, Let):
        params = "(" + _binders(node.params) + ")" if node.params else ""
        typ = f": {show(node.type)}" if node.type is not None else ""
        head = (show(node.pattern) if node.pattern is not None else
                f"`{node.name}`" if node.name in ops.RESERVED else node.name)
        term = f" termination_by {show(node.termination)}" if node.termination is not None else ""
        return f"let {'rec ' if node.rec else ''}{head}{params}{typ} = {show(node.value)}{term}; {show(node.body)}"
    if isinstance(node, Match):
        arms = " ".join(f"| {', '.join(show(p) for p in pats)} => {_low(e) if k + 1 < len(node.arms) else show(e)}"
                        for k, (pats, e) in enumerate(node.arms))
        return f"match {', '.join(show(s) for s in node.scrutinees)} with {arms}"
    if isinstance(node, Tuple_):
        return "(" + ", ".join(show(i) for i in node.items) + ")"
    if isinstance(node, ListLit):
        return ("#[" if node.array else "[") + ", ".join(show(i) for i in node.items) + "]"
    if isinstance(node, Anon):
        return "⟨" + ", ".join(show(i) for i in node.items) + "⟩"
    if isinstance(node, Ascribe):
        return f"({show(node.expr)} as {show(node.type)})"
    if isinstance(node, Abs):
        return f"{ABS_FUNCS[node.kind]}({show(node.arg)})"
    raise TypeError(type(node).__name__)


def _binders(names) -> str:
    def one(n, t):
        if n == "<pat>":
            return show(t)
        if n == "[]":
            return f"[{show(t)}]"
        if n.startswith("{"):
            return f"{{{n[1:-1]}: {show(t)}}}" if t is not None else n
        return f"({n}: {show(t)})" if t is not None else n
    return ", ".join(one(n, t) for n, t in names)


# --- parsing ------------------------------------------------------------------------------------------------------

_TOKEN = re.compile(r"""
    (?P<ws>\s+)
  | (?P<num>0[xX][0-9a-fA-F]+|0[bB][01]+|\d+(?:\.\d+)?)
  | (?P<char>'(?:\\.|[^'\\])')
  | (?P<sstr>'(?:\\.|[^'\\])*')
  | (?P<str>"(?:\\.|[^"\\])*")
  | (?P<esc>`[^`]+`)
  | (?P<op><==>|==>|===|!==|&&&|\|\|\||>>>|<<<|~~~|//|:=|=>|==|!=|<=|>=|\*\*|\+\+|::|&&|\|\||[-+*/%<>!↑·=|⊕])
  | (?P<punct>\#\[|[()\[\]{},:;.⟨⟩?])
  | (?P<lean>[¬∧∨→↔≤≥≠])
  | (?P<ident>[^\W\d][\w']*(?:\.[^\W\d][\w']*)*(?:[!?](?![\w=]))?)
""", re.VERBOSE | re.UNICODE)

#: L_spec infix spelling -> Lean operator
_INFIX = {ops.BINOPS.get(op, op): op for op in INFIX if op not in ("<|", "|>", "$", "×")}
_INFIX.update({"<=": "≤", ">=": "≥", "//": "/", "implies": "→"})  # Python's `//`: integer division
#: Lean's logical and comparison symbols, read as their L_spec spelling
_LEAN_SYMBOLS = {"¬": "not", "∧": "and", "∨": "or", "→": "==>", "↔": "<==>", "≤": "<=", "≥": ">=", "≠": "!="}


def tokenize(text: str):
    out, spans, pos = [], [], 0
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m:
            raise Unsupported(f"unexpected character {text[pos]!r}")
        pos = m.end()
        if m.lastgroup == "ws":
            continue
        if m.lastgroup == "sstr":                          # Python's 'text' (not one character): a string
            inner = m.group()[1:-1].replace("\\'", "'").replace('"', '\\"')
            out.append(f'"{inner}"')
        elif m.lastgroup == "lean":                        # Lean's symbol: the same operator
            out.append(_LEAN_SYMBOLS[m.group()])
        else:
            out.append(m.group())
        spans.append((m.start(), m.end()))
    return out, spans


class _Parser:
    def __init__(self, text: str):
        self.toks, self.spans = tokenize(text)
        self.k = 0

    def peek(self, offset: int = 0) -> Optional[str]:
        return self.toks[self.k + offset] if self.k + offset < len(self.toks) else None

    def next(self) -> str:
        if self.k >= len(self.toks):
            raise Unsupported("unexpected end")
        self.k += 1
        return self.toks[self.k - 1]

    def expect(self, tok: str):
        got = self.next()
        if got != tok:
            raise Unsupported(f"expected {tok!r}, found {got!r}")

    def adjacent(self) -> bool:
        return 0 < self.k < len(self.toks) and self.spans[self.k][0] == self.spans[self.k - 1][1]

    # --- expressions ---
    def expr(self, min_prec: int = 0) -> Node:
        left = self.binops(max(min_prec, 1))
        if min_prec <= 0 and self.peek() == "if":           # `a if c else b`
            self.next()
            hyp = None
            if self.peek(1) == ":=":
                hyp = self.next()
                self.next()
            cond = self.expr(1)
            self.expect("else")
            return If(cond, left, self.expr(0), hyp)
        return left

    def infix(self) -> Optional[str]:
        tok = self.peek()
        if tok == "not" and self.peek(1) == "in":
            return "not in"
        return tok if tok in _INFIX else None

    def binops(self, min_prec: int) -> Node:
        left = self.prefix()
        last = None                         # the right operand of a comparison just read: `a < b < c` chains
        while True:
            spelled = self.infix()
            if spelled is None:
                return left
            op = _INFIX[spelled]
            prec, right_assoc = INFIX[op]
            if prec < min_prec:
                return left
            self.next()
            if spelled == "not in":
                self.next()
            right = self.binops(prec if right_assoc else prec + 1)
            if op in CHAIN and last is not None:                  # Python: `a < b < c` is `a < b and b < c`
                left = BinOp("∧", left, BinOp(op, last, right))
            else:
                left = BinOp(op, left, right)
            last = right if op in CHAIN else None

    def prefix(self) -> Node:
        tok = self.peek()
        if tok in ("lambda", "forall", "exists"):
            return self.binder()
        if tok == "let":
            return self.let()
        if tok == "if":                                     # Lean's `if c then a else b` (`else` reaches right)
            self.next()
            hyp = None
            if self.peek(1) == ":=":
                hyp = self.next()
                self.next()
            cond = self.expr(0)
            self.expect("then")
            then = self.expr(0)
            if self.peek() != "else" and hyp is None:      # `if c then p` with no else: a statement, `c ==> p`
                return BinOp("→", cond, then)
            self.expect("else")
            return If(cond, then, self.expr(0), hyp)
        if tok == "match":
            return self.match()
        if tok in ops.UNOPS_INV and tok != "-" or tok == "-" and self.peek(1) is not None:
            if tok == "not" and self.peek(1) == "in":
                raise Unsupported("`not in` without a left operand")
            self.next()
            lean = ops.UNOPS_INV[tok]
            return UnOp(lean, self.binops(PREFIX[lean]) if PREFIX[lean] < 1024 else self.postfix(self.atom()))
        return self.postfix(self.atom())

    def atom(self) -> Node:
        tok = self.next()
        if tok == "(":
            if self.peek() == ")":
                self.next()
                return Name("()")
            first = self.expr()
            if self.peek() == "as":
                self.next()
                node = Ascribe(first, self.expr())
                self.expect(")")
                return node
            items = [first]
            while self.peek() == ",":
                self.next()
                items.append(self.expr())
            self.expect(")")
            return Tuple_(items) if len(items) > 1 else first
        if tok in ("[", "#["):
            items = self.items("]")
            if len(items) == 1 and isinstance(items[0], _Gen):
                if tok == "#[":
                    raise Unsupported("an array comprehension: write the list comprehension and `array_of(...)`")
                return items[0].as_list()
            return ListLit(items, array=tok == "#[")
        if tok == "⟨":
            return Anon(self.items("⟩"))
        if tok == "·":
            return Name("·")
        if tok[0].isdigit():
            return Num(tok)
        if tok[0] == "'":
            return Char(tok[1:-1])
        if tok[0] == '"':
            return Str(tok[1:-1])
        if tok[0] == "`":
            return _dotted(tok[1:-1])
        if tok[0].isalpha() or tok[0] == "_":
            if tok in ops.KEYWORDS:
                raise Unsupported(f"unexpected {tok!r}")
            if "." not in tok:
                if tok in _SCOPE:
                    return Name(tok)             # a variable of the goal, whatever L_spec name it spells
                return _SpecName(tok)            # resolved by what follows: `list[int]`, `list(s)`, `list`
            node = _dotted(tok)
            return _rename_fields(node)
        raise Unsupported(f"unexpected {tok!r}")

    def items(self, close: str) -> List[Node]:
        out = []
        if self.peek() == close:
            self.next()
            return out
        out.append(self.expr())
        if self.peek() == "for":                               # `[f(x) for x in l if p(x)]`, `sum(f(x) for x in l)`
            out[0] = self.comprehension(out[0])
            self.expect(close)
            return out
        while self.peek() == ",":
            self.next()
            out.append(self.expr())
        self.expect(close)
        return out

    def comprehension(self, elem: Node) -> "_Gen":
        self.next()
        var = self.next()
        if not re.fullmatch(r"[^\W\d][\w']*", var) or var in ops.KEYWORDS:
            raise Unsupported("a comprehension over a pattern (`for i, x in ...`): use one variable, e.g. an index "
                              "`for i in range(len(l))`")
        self.expect("in")
        source = self.binops(1)
        cond = None
        if self.peek() == "if":
            self.next()
            cond = self.binops(1)
        if self.peek() == "for":
            raise Unsupported("a comprehension with two `for`: write `l.flat_map(lambda x: [...])`")
        return _Gen(elem, var, source, cond)

    def postfix(self, node: Node) -> Node:
        while True:
            tok = self.peek()
            if tok == "(" and self.adjacent():
                self.next()
                node = self.call(node, self.items(")"))
            elif tok == "." and self.adjacent():
                self.next()
                field = self.next()
                if field.startswith("`"):
                    field = field[1:-1]
                else:
                    field = _lean_field(field)
                for part in field.split("."):
                    node = Dot(_resolve(node), part)
            elif tok == "[" and self.adjacent():
                self.next()
                node = self.subscript(node)
            else:
                return _resolve(node)

    def call(self, fn: Node, args: List[Node]) -> Node:
        if isinstance(fn, _SpecName) and fn.id in ("any", "all") and len(args) == 1:  # `any(p(x) for x in l)`
            arg = args[0]
            if isinstance(arg, _Gen):
                return App(Dot(arg.source_list(), fn.id), [arg.lam(arg.elem)])
            return App(Dot(arg, fn.id), [Binder("fun", [("_b", None)], None, Name("_b"))])
        args = [a.as_list() if isinstance(a, _Gen) else a for a in args]
        if isinstance(fn, Dot) and fn.field in STRING_ARGS:     # Python's ' ' is a str: `s.split(' ')`, `','.join(l)`
            args = [Str(a.text) if isinstance(a, Char) else a for a in args]
            if fn.field == "intercalate" and isinstance(fn.obj, Char):
                fn = Dot(Str(fn.obj.text), fn.field)
        if isinstance(fn, _SpecName) and fn.id == "range" and len(args) > 1:         # `range(a, b)`
            if len(args) > 2:
                raise Unsupported("`range` with a step: write `range(n).map(lambda k: a + k * step)`")
            return App(Name("List.range'"), [args[0], BinOp("-", args[1], args[0])])
        if isinstance(fn, _SpecName) and fn.id in ops.METHOD_FUNCS_INV and args:     # `len(l)` is `l.length`
            dot = Dot(args[0], ops.METHOD_FUNCS_INV[fn.id])
            return App(dot, args[1:]) if len(args) > 1 else dot
        if isinstance(fn, _SpecName) and fn.id in ("max", "min") and len(args) == 1:  # of a list (default if empty)
            return Dot(Dot(args[0], fn.id + "?"), "get!")
        if isinstance(fn, _SpecName) and fn.id in PY_FUNCS and len(args) == 2:      # `map(f, l)` is `l.map f`
            return App(Dot(args[1], fn.id), [args[0]])
        if isinstance(fn, _SpecName) and fn.id in ops.CALL_NAMES_INV and args:      # `bool(p)` is `decide p`
            return App(Name(ops.CALL_NAMES_INV[fn.id]), args)
        if isinstance(fn, _SpecName) and fn.id in ABS_INV and len(args) == 1:
            return Abs(args[0], ABS_INV[fn.id])
        fn = _resolve(fn)
        if isinstance(fn, Dot) and not args:                                        # `s.upper()` is `s.toUpper`
            return fn
        return App(fn, args)

    def subscript(self, obj: Node) -> Node:
        if isinstance(obj, _SpecName) and obj.id == "tuple":
            parts = self.items("]")
            node = parts[-1]
            for p in reversed(parts[:-1]):
                node = BinOp("×", p, node)
            return node
        obj = _resolve(obj)
        if isinstance(obj, Name) and obj.id in TYPE_CTORS:                           # `list[int]`
            arg = self.expr()
            self.expect("]")
            return App(obj, [arg])
        if self.peek() in (":", "::"):                                                # `l[:k]`, `l[::-1]`
            double = self.next() == "::"
            if double or self.peek() == ":":
                if not double:
                    self.next()
                step = self.expr()
                self.expect("]")
                if isinstance(step, UnOp) and step.op == "-" and isinstance(step.arg, Num) and step.arg.text == "1":
                    return Dot(obj, "reverse")
                raise Unsupported("a slice with a step other than `[::-1]`")
            k = self.expr()
            self.expect("]")
            return App(Dot(obj, "take"), [_from_end(obj, k)])
        if self.peek() == "[":                                                        # `l[[i]]`
            self.next()
            idx = self.expr()
            self.expect("]")
            self.expect("]")
            return Index(obj, idx, "")
        idx = self.expr()
        if self.peek() == ":":                                                        # `l[k:]`, `l[a:b]`
            self.next()
            if self.peek() == "]":
                self.next()
                return App(Dot(obj, "drop"), [_from_end(obj, idx)])
            end = self.expr()
            self.expect("]")
            start, end = _from_end(obj, idx), _from_end(obj, end)
            return App(Dot(App(Dot(obj, "drop"), [start]), "take"), [BinOp("-", end, start)])
        self.expect("]")
        if self.peek() == "?" and self.adjacent():
            self.next()
            return Index(obj, _from_end(obj, idx), "?")
        return Index(obj, _from_end(obj, idx), "!")

    def binders(self):
        out = []
        while True:
            tok = self.peek()
            if tok == "(" and self.peek(2) == ":":                   # `(x: T)`: the name as written
                self.next()
                name = self.next().strip("`")
                self.next()
                typ = self.expr()
                self.expect(")")
                out.append((name, typ))
            elif tok == "(":
                self.next()
                first = self.expr()
                if self.peek() == ":":
                    self.next()
                    typ = self.expr()
                    self.expect(")")
                    out.append((show_name(first), typ))
                else:                                                # `(a, b)`: a pattern
                    items = [first]
                    while self.peek() == ",":
                        self.next()
                        items.append(self.expr())
                    self.expect(")")
                    out.append(("<pat>", Tuple_(items)))
            elif tok == "⟨":
                self.next()
                out.append(("<pat>", Anon(self.items("⟩"))))
            elif tok == "{":
                self.next()
                name = self.next()
                self.expect(":")
                typ = self.expr()
                self.expect("}")
                out.append(("{" + name + "}", typ))
            elif tok == "[":
                self.next()
                inst = self.expr()
                self.expect("]")
                out.append(("[]", inst))
            elif tok and (tok[0].isalpha() or tok[0] in "_`"):
                name = self.next()
                out.append((name.strip("`"), None))
            else:
                raise Unsupported(f"binder {tok!r}")
            if self.peek() != ",":
                return out
            self.next()

    def binder(self) -> Node:
        kind = {"lambda": "fun", "forall": "∀", "exists": "∃"}[self.next()]
        names = self.binders()
        bound = None
        tok = self.peek()
        if kind != "fun" and (tok in BOUNDS_INV or tok == "not" and self.peek(1) == "in"):
            spelled = self.next()
            if spelled == "not":
                self.next()
                spelled = "not in"
            bound = (BOUNDS_INV[spelled], self.binops(51))
        self.expect(":")
        body = self.expr()
        if (kind != "fun" and self.peek() == "," and bound is None and len(names) == 1 and names[0][1] is None
                and not names[0][0].startswith(("<", "[", "{"))):        # Lean's `forall j: nat, body`
            self.next()
            names, body = [(names[0][0], body)], self.expr()
        return Binder(kind, names, bound, body)

    def assign(self):
        """`=` in a `let`; Lean's `:=` is accepted too (models write it)."""
        if self.peek() == ":=":
            self.next()
        else:
            self.expect("=")

    def let(self) -> Node:
        self.next()
        rec = self.peek() == "rec"
        if rec:
            self.next()
        if self.peek() in ("(", "⟨"):                 # `let (i, j) = result; ...`
            close = ")" if self.next() == "(" else "⟩"
            items = self.items(close)
            pattern = Tuple_(items) if close == ")" else Anon(items)
            self.assign()
            value = self.expr()
            self.expect(";")
            return Let("<pat>", None, value, self.expr(), [], rec, pattern)
        name = self.next()
        if name.startswith("`"):
            name = name[1:-1]
        params = []
        if self.peek() == "(" and self.adjacent():
            self.next()
            params = self.binders()
            self.expect(")")
        typ = None
        if self.peek() == ":":
            self.next()
            typ = self.binops(1)
        self.assign()
        value = self.expr()
        termination = None
        if self.peek() == "termination_by":
            self.next()
            termination = self.expr()
        self.expect(";")
        return Let(name, typ, value, self.expr(), params, rec, None, termination)

    def match(self) -> Node:
        self.next()
        scrutinees = [self.expr()]
        while self.peek() == ",":
            self.next()
            scrutinees.append(self.expr())
        self.expect("with")
        arms = []
        while self.peek() == "|":
            self.next()
            pats = [self.binops(51)]
            while self.peek() == ",":
                self.next()
                pats.append(self.binops(51))
            while self.peek() == "|":                # alternatives `| [] | [_] => e`
                if len(pats) > 1:
                    raise Unsupported("alternatives of several patterns")
                self.next()
                pats = [BinOp("|", pats[0], self.binops(51))]
            self.expect("=>")
            arms.append((pats, self.expr()))
        return Match(scrutinees, arms)


def _from_end(obj: Node, k: Node) -> Node:
    """Python's negative index or slice bound: `l[-k]` is `l[len(l) - k]`."""
    if isinstance(k, UnOp) and k.op == "-":
        return BinOp("-", Dot(obj, "length"), k.arg)
    return k


class _Gen(Node):
    """`elem for var in source if cond`, before it is read as a list (`source.filter(...).map(...)`) or an `any`/`all`."""
    def __init__(self, elem, var, source, cond):
        self.elem, self.var, self.source, self.cond = elem, var, source, cond

    def lam(self, body: Node) -> Node:
        return Binder("fun", [(self.var, None)], None, body)

    def source_list(self) -> Node:
        return App(Dot(self.source, "filter"), [self.lam(self.cond)]) if self.cond is not None else self.source

    def as_list(self) -> Node:
        base = self.source_list()
        if isinstance(self.elem, Name) and self.elem.id == self.var:
            return base
        return App(Dot(base, "map"), [self.lam(self.elem)])


class _SpecName(Node):
    """A plain L_spec name before it is resolved: `list` is `List` in `list[int]` and `toList` in `list(s)`."""
    def __init__(self, id):
        self.id = id


def _resolve(node: Node) -> Node:
    return Name(ops.NAMES_INV.get(node.id, node.id)) if isinstance(node, _SpecName) else node


def _rename_fields(node: Node) -> Node:
    """`l.index` read as one dotted name: its fields are methods, renamed back to Lean's (`idxOf`)."""
    if isinstance(node, Dot):
        return Dot(_rename_fields(node.obj), _lean_field(node.field))
    return node


def _lean_field(field: str) -> str:
    """The Lean field an L_spec method name stands for: `index` is `idxOf`; a function written as a method,
    `l.sorted()` / `l.len()`, is the function (`sorted(l)`); another language's spelling, `indexOf`, is read too."""
    return ops.METHODS_INV.get(field, ops.METHOD_FUNCS_INV.get(field, ops.METHOD_ALIASES.get(field, field)))


def show_name(node: Node) -> str:
    """A binder's name, as written (a binder named `digits` is a variable, not the library's `digits`)."""
    if isinstance(node, (Name, _SpecName)):
        return node.id
    raise Unsupported("a binder must be a name")


#: names that are variables where the text is read (a goal's inputs, a loop's state): such a name is that variable,
#: never the L_spec name it happens to spell (an input called `string` is not `string(...)`)
_SCOPE: frozenset = frozenset()


def show_in(node: Node, scope=()) -> str:
    """``show`` for text read back with ``parse(text, scope)``: an L_spec name that is a variable in ``scope`` is
    printed with Lean's spelling instead (``String.mk(s)``, not ``string(s)``, where an input is called ``string``)."""
    global _SCOPE
    saved, _SCOPE = _SCOPE, frozenset(scope)
    try:
        return show(node)
    finally:
        _SCOPE = saved


def parse(text: str, scope=()) -> Node:
    global _SCOPE
    saved, _SCOPE = _SCOPE, frozenset(scope)
    try:
        p = _Parser(text)
        node = p.expr()
        if p.peek() is not None:
            raise Unsupported(f"trailing {p.peek()!r}")
        return _resolve(node)
    finally:
        _SCOPE = saved
