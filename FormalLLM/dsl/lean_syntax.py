"""The Lean subset the derivations are written in: a parser (Lean text -> ``ast``) and a printer (``ast`` -> Lean text).

Not a Lean parser: it reads the expressions of a derivation (values, invariants, guards, conditions, lemma statements)
with Lean 4's precedences, and raises ``Unsupported`` on anything else, so that the corpus check can count what the
L_spec does not cover yet. The printer parenthesises every compound operand, so ``print(parse(t))`` may differ from
``t`` in parentheses only; the corpus check has Lean prove the two equal."""
import re
from typing import List, Optional

from FormalLLM.dsl.ast import (Abs, Anon, App, Ascribe, Binder, BinOp, Char, Dot, If, Index, Let, ListLit, Match,
                               Name, Node, Num, Str, Tuple_, UnOp)


class Unsupported(Exception):
    """A construct outside the subset (``match``, structure instances, ...); the message names it."""


#: binary operators: precedence, and whether the right operand binds at the same level (right associative)
INFIX = {
    "<|": (10, True), "|>": (10, False), "$": (10, True),
    "↔": (20, False), "→": (25, True),
    "∨": (30, True), "||": (30, False), "∧": (35, True), "&&": (35, False), "×": (35, True),
    "=": (50, False), "≠": (50, False), "==": (50, False), "!=": (50, False), "<": (50, False), ">": (50, False),
    "≤": (50, False), "≥": (50, False), "<=": (50, False), ">=": (50, False), "∈": (50, False), "∉": (50, False),
    "∣": (50, False), "⊆": (50, False), "~": (50, False), "<:+:": (50, False), "<+:": (50, False),
    "<:+": (50, False), "<+": (50, False),
    "^^^": (58, False), "&&&": (58, False), "|||": (55, False), ">>>": (75, False), "<<<": (75, False),
    "++": (65, False), "::": (67, True), "+": (65, False), "-": (65, False),
    "*": (70, False), "/": (70, False), "%": (70, False), "^": (75, True), "∘": (90, False),
}
PREFIX = {"¬": 40, "-": 75, "!": 40, "↑": 1024}         # `!b` reads its argument at 40: `!decide (a < b)`
KEYWORDS = {"fun", "λ", "∀", "∃", "if", "then", "else", "let", "in", "match", "with", "do", "have", "show", "by"}

_TOKEN = re.compile(r"""
    (?P<nl>\n)
  | (?P<ws>[ \t\r]+)
  | (?P<num>\d+(?:\.\d+)?)
  | (?P<char>'(?:\\.|[^'\\])')
  | (?P<str>"(?:\\.|[^"\\])*")
  | (?P<op><:\+:|<\+:|<:\+|<\+|\^\^\^|&&&|\|\|\||>>>|<<<|<\||\|>\.|\|>|:=|=>|\|\||&&|==|!=|<=|>=|\+\+|::|↦|[-+*/%^=<>≤≥≠∈∉∣⊆~∘↔→∧∨¬×!↑·|$])
  | (?P<punct>\#\[|⌋₊|⌉₊|[()\[\]{},:;.⟨⟩?@⌊⌋⌈⌉])
  | (?P<ident>[^\W\d]['\w]*(?:\.[^\W\d]['\w]*)*(?:[!?](?!=))?|[∀∃λ])
""", re.VERBOSE | re.UNICODE)


def tokenize(text: str):
    """The tokens, and for each its start and end offset (``a[i]`` indexes only when ``[`` touches ``a``)."""
    out, spans, pos = [], [], 0
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m:
            raise Unsupported(f"unexpected character {text[pos]!r}")
        pos = m.end()
        if m.lastgroup == "ws":
            continue
        out.append("\n" if m.lastgroup == "nl" else m.group())
        spans.append((m.start(), m.end()))
    return out, spans


class _Parser:
    def __init__(self, text: str):
        self.toks, self.spans = tokenize(text)
        self.k = 0
        self.nl_stops = 0                        # inside a `let` value a line break ends the value

    # --- tokens ---
    def peek(self, offset: int = 0) -> Optional[str]:
        k, seen = self.k, -1
        while k < len(self.toks):
            if self.toks[k] == "\n":
                if self.nl_stops:
                    if seen + 1 == offset:
                        return "\n"
                    seen += 1
                k += 1
                continue
            seen += 1
            if seen == offset:
                return self.toks[k]
            k += 1
        return None

    def next(self) -> str:
        while self.k < len(self.toks) and self.toks[self.k] == "\n" and not self.nl_stops:
            self.k += 1
        if self.k >= len(self.toks):
            raise Unsupported("unexpected end")
        tok = self.toks[self.k]
        self.k += 1
        return tok

    def expect(self, tok: str):
        got = self.next()
        if got != tok:
            raise Unsupported(f"expected {tok!r}, found {got!r}")

    # --- expressions ---
    def expr(self, min_prec: int = 0) -> Node:
        left = self.prefix()
        while True:
            op = self.peek()
            if op == "|>." and min_prec <= 10:
                # `x |>.f a b` is `x.f a b`
                self.next()
                node: Node = Dot(left, self.next())
                args = []
                while self.starts_atom(self.peek()):
                    if self.peek() in ("fun", "λ"):
                        args.append(self.lam())
                        break
                    args.append(self.postfix(self.atom()))
                left = self.postfix(App(node, args) if args else node)
                continue
            if op not in INFIX:
                return left
            prec, right_assoc = INFIX[op]
            if prec < min_prec:
                return left
            self.next()
            right = self.expr(prec if right_assoc else prec + 1)
            left = BinOp(op, left, right)

    def prefix(self) -> Node:
        tok = self.peek()
        if tok in ("fun", "λ"):
            return self.lam()
        if tok in ("∀", "∃"):
            return self.quant()
        if tok == "if":
            return self.ite()
        if tok == "let":
            return self.let()
        if tok == "match":
            return self.match()
        if tok in PREFIX and not (tok == "-" and self.peek(1) is None):
            self.next()
            return UnOp(tok, self.expr(PREFIX[tok]) if PREFIX[tok] < 1024 else self.postfix(self.atom()))
        return self.application()

    def application(self) -> Node:
        fn = self.postfix(self.atom())
        args = []
        while self.starts_atom(self.peek()):
            if self.peek() in ("fun", "λ"):
                args.append(self.lam())          # a trailing `fun` is the last argument (`l.all fun x => ...`)
                break
            args.append(self.postfix(self.atom()))
        return App(fn, args) if args else fn

    @staticmethod
    def starts_atom(tok: Optional[str]) -> bool:
        if tok is None or tok in KEYWORDS - {"fun", "λ"} or tok == "\n":
            return False
        return tok in ("(", "[", "#[", "⟨", "fun", "λ", "·", "↑", "⌊", "⌈") or tok[0].isdigit() or tok[0] in "'\"" or \
            (tok[0].isalpha() or tok[0] == "_") and tok not in INFIX

    def atom(self) -> Node:
        tok = self.next()
        if tok == "(":
            return self.paren()
        if tok in ("[", "#["):
            items = self.items("]")
            return ListLit(items, array=tok == "#[")
        if tok == "⟨":
            return Anon(self.items("⟩"))
        if tok in ("|", "⌊", "⌈"):
            arg = self.expr()
            close = self.next()
            if close not in ({"|": ("|",), "⌊": ("⌋", "⌋₊"), "⌈": ("⌉", "⌉₊")}[tok]):
                raise Unsupported(f"{tok} closed by {close!r}")
            return Abs(arg, tok + ("₊" if close.endswith("₊") else ""))     # `⌊x⌋₊`: the natural-number floor
        if tok == "{":
            raise Unsupported("structure instance / set-builder")
        if tok == "↑":
            return UnOp("↑", self.postfix(self.atom()))
        if tok == "·":
            return Name("·")
        if tok[0].isdigit():
            return Num(tok)
        if tok[0] == "'":
            return Char(tok[1:-1])
        if tok[0] == '"':
            return Str(tok[1:-1])
        if tok[0].isalpha() or tok[0] == "_":
            if tok in KEYWORDS:
                raise Unsupported(tok)
            return _dotted(tok)
        raise Unsupported(f"unexpected {tok!r}")

    def postfix(self, node: Node) -> Node:
        while True:
            tok = self.peek()
            if tok == "." and self.adjacent():
                self.next()
                for part in self.next().split("."):        # `p.1.2` comes as `p`, `.`, `1.2`
                    node = Dot(node, part)
            elif tok == "[" and self.adjacent():
                self.next()
                idx = self.expr()
                self.expect("]")
                kind = ""
                if self.peek() in ("!", "?") and self.adjacent():
                    kind = self.next()
                node = Index(node, idx, kind)
            else:
                return node

    def adjacent(self) -> bool:
        """The next token follows the previous one without a space (`a[i]` indexes, `f [1, 2]` applies)."""
        k = self.k
        while k < len(self.toks) and self.toks[k] == "\n":
            k += 1
        return 0 < k < len(self.toks) and self.spans[k][0] == self.spans[self.k - 1][1]

    def paren(self) -> Node:
        if self.peek() == ")":
            self.next()
            return Name("()")
        self.nl_stops, saved = 0, self.nl_stops
        first = self.expr()
        if self.peek() == ":":
            self.next()
            node = Ascribe(first, self.expr())
            self.expect(")")
            self.nl_stops = saved
            return node
        items = [first]
        while self.peek() == ",":
            self.next()
            items.append(self.expr())
        self.expect(")")
        self.nl_stops = saved
        return Tuple_(items) if len(items) > 1 else _Paren(first)

    def items(self, close: str) -> List[Node]:
        saved, self.nl_stops = self.nl_stops, 0
        out = []
        if self.peek() == close:
            self.next()
        else:
            out.append(self.expr())
            while self.peek() == ",":
                self.next()
                out.append(self.expr())
            self.expect(close)
        self.nl_stops = saved
        return out

    def binders(self, stop: set):
        """`x y`, `(x : T)`, `(x y : T)`, `x : T`; also `(a, b)` / `⟨a, b⟩` patterns (for `fun`)."""
        out, pattern = [], None
        while self.peek() not in stop:
            tok = self.peek()
            if tok == "(" and self.peek(2) == ",":
                self.next()                          # a pattern takes its place among the binders: `fun acc (s, e) => ...`
                out.append(("<pat>", Tuple_(self.items(")"))))
            elif tok == "⟨":
                self.next()
                out.append(("<pat>", Anon(self.items("⟩"))))
            elif tok == "[":
                self.next()                          # an instance binder `[LinearOrder β]`
                inst = self.expr()
                self.expect("]")
                out.append(("[]", inst))
            elif tok in ("(", "{"):
                # `{α : Type}` is implicit: the printer writes every binder explicitly typed, which Lean accepts
                close = ")" if tok == "(" else "}"
                self.next()
                names = []
                while self.peek() not in (":", close):
                    names.append(self.next())
                typ = None
                if self.peek() == ":":
                    self.next()
                    typ = self.expr()
                self.expect(close)
                out += [(n if tok == "(" else "{" + n + "}", typ) for n in names]
            elif tok == ":":
                self.next()
                typ = self.expr(26)              # `∀ x : T, ...`: the type ends before `,` / `=>`
                out = [(n, typ if t is None else t) for n, t in out]
            elif tok == "_" or tok and (tok[0].isalpha() or tok[0] == "_") and tok not in KEYWORDS:
                out.append((self.next(), None))
            else:
                return out, pattern
        return out, pattern

    def lam(self) -> Node:
        self.next()
        names, pattern = self.binders({"=>", "↦"})
        if self.peek() not in ("=>", "↦"):
            raise Unsupported(f"fun binder {self.peek()!r}")
        self.next()
        return Binder("fun", names, None, self.expr(), pattern)

    def quant(self) -> Node:
        kind = self.next()
        names, _ = self.binders({",", "∈", "∉", "<", "≤", ">", "≥"})
        bound = None
        if self.peek() in ("∈", "∉", "<", "≤", ">", "≥"):
            op = self.next()
            bound = (op, self.expr(51))
        self.expect(",")
        if not names:
            raise Unsupported(f"{kind} without variables")
        return Binder(kind, names, bound, self.expr())

    def ite(self) -> Node:
        self.next()
        hyp = None
        if self.peek(1) == ":" and self.peek() and self.peek()[0].isalpha():
            hyp = self.next()
            self.next()
        cond = self.expr()
        self.expect("then")
        yes = self.expr()
        self.expect("else")
        return If(cond, yes, self.expr(), hyp)

    def match(self) -> Node:
        """`match a, b with | p, q => e | _ => f`: patterns are read as expressions."""
        self.next()
        scrutinees = [self.expr()]
        while self.peek() == ",":
            self.next()
            scrutinees.append(self.expr())
        self.expect("with")
        arms = []
        while self.peek() == "|":
            self.next()
            pats = [self.expr(51)]
            while self.peek() == ",":
                self.next()
                pats.append(self.expr(51))
            self.expect("=>")
            arms.append((pats, self.expr()))
        if not arms:
            raise Unsupported("match without arms")
        return Match(scrutinees, arms)

    def let(self) -> Node:
        self.next()
        name = self.next()
        params, _ = self.binders({":", ":="})
        typ = None
        if self.peek() == ":":
            self.next()
            typ = self.expr(26)
        self.expect(":=")
        self.nl_stops += 1
        value = self.expr()
        self.nl_stops -= 1
        if self.peek() in (";", "\n", "in"):
            self.next()
        return Let(name, typ, value, self.expr(), params)


class _Paren(Node):
    """Parentheses the source wrote; dropped by ``parse`` (the printer adds its own)."""
    def __init__(self, inner):
        self.inner = inner


#: dotted identifiers whose first part is a namespace, not a variable (`List.range`, `Refine.maxlist_nat`)
NAMESPACES = {"List", "Array", "String", "Nat", "Int", "Char", "Bool", "Option", "Prod", "Float", "Rat", "Real",
              "Finset", "Multiset", "Fin", "Refine", "Function", "Classical", "Decidable", "Or", "And", "Iff", "Eq",
              "Std", "Sum", "Subtype", "Except", "Id", "IO", "Ordering", "UInt8", "UInt32", "UInt64"}


def _dotted(tok: str) -> Node:
    parts = tok.split(".")
    if len(parts) == 1 or parts[0] in NAMESPACES or parts[0][:1].isupper():
        return Name(tok)
    node: Node = Name(parts[0])
    for f in parts[1:]:
        node = Dot(node, f)
    return node


def _unparen(node):
    if isinstance(node, _Paren):
        return _unparen(node.inner)
    if not isinstance(node, Node):
        return node
    for key, value in vars(node).items():
        if isinstance(value, list):
            setattr(node, key, [_unparen_any(v) for v in value])
        elif isinstance(value, tuple):
            setattr(node, key, _unparen_any(value))
        else:
            setattr(node, key, _unparen(value))
    return node


def _unparen_any(v):
    if isinstance(v, tuple):
        return tuple(_unparen_any(x) for x in v)
    if isinstance(v, list):
        return [_unparen_any(x) for x in v]
    return _unparen(v)


def parse(text: str) -> Node:
    p = _Parser(text)
    node = p.expr()
    if p.peek() is not None:
        raise Unsupported(f"trailing {p.peek()!r}")
    return _unparen(node)


# --- printing -----------------------------------------------------------------------------------------------------

_ATOMS = (Name, Num, Char, Str, ListLit, Tuple_, Anon, Abs)


def _arg(node: Node) -> str:
    """``node`` as an operand: parenthesised unless it is atomic (or a postfix chain on an atom)."""
    text = show(node)
    if isinstance(node, _ATOMS) or isinstance(node, (Dot, Index)):
        return text
    return f"({text})"


def show(node: Node) -> str:
    if isinstance(node, Name):
        return node.id
    if isinstance(node, Num):
        return node.text
    if isinstance(node, Char):
        return f"'{node.text}'"
    if isinstance(node, Str):
        return f'"{node.text}"'
    if isinstance(node, App):
        return " ".join([_arg(node.fn)] + [_arg(a) for a in node.args])
    if isinstance(node, Dot):
        return f"{_arg(node.obj)}.{node.field}"
    if isinstance(node, Index):
        return f"{_arg(node.obj)}[{show(node.idx)}]{node.kind}"
    if isinstance(node, BinOp):
        return f"{_arg(node.left)} {node.op} {_arg(node.right)}"
    if isinstance(node, UnOp):
        return f"{node.op}{'' if node.op in '!↑-' else ' '}{_arg(node.arg)}"
    if isinstance(node, Binder):
        if node.pattern is not None:
            head = show(node.pattern)
        else:
            head = _binders(node.vars)
        if node.bound:
            head += f" {node.bound[0]} {_arg(node.bound[1])}"
        sep = " =>" if node.kind == "fun" else ","
        return f"{node.kind} {head}{sep} {show(node.body)}"
    if isinstance(node, If):
        hyp = f"{node.hyp} : " if node.hyp else ""
        return f"if {hyp}{show(node.cond)} then {show(node.then)} else {show(node.other)}"
    if isinstance(node, Let):
        params = " " + _binders(node.params) if node.params else ""
        typ = f" : {show(node.type)}" if node.type is not None else ""
        return f"let {node.name}{params}{typ} := {show(node.value)}; {show(node.body)}"
    if isinstance(node, Match):
        arms = " ".join(f"| {', '.join(show(p) for p in pats)} => {show(e)}" for pats, e in node.arms)
        return f"match {', '.join(show(s) for s in node.scrutinees)} with {arms}"
    if isinstance(node, Tuple_):
        return "(" + ", ".join(show(i) for i in node.items) + ")"
    if isinstance(node, ListLit):
        return ("#[" if node.array else "[") + ", ".join(show(i) for i in node.items) + "]"
    if isinstance(node, Anon):
        return "⟨" + ", ".join(show(i) for i in node.items) + "⟩"
    if isinstance(node, Ascribe):
        return f"({show(node.expr)} : {show(node.type)})"
    if isinstance(node, Abs):
        close = dict(zip('|⌊⌈', '|⌋⌉'))[node.kind[0]] + node.kind[1:]
        return f"{node.kind[0]}{show(node.arg)}{close}"
    raise TypeError(type(node).__name__)


def _binders(names) -> str:
    def one(n, t):
        if n == "<pat>":
            return show(t)
        if n == "[]":
            return f"[{show(t)}]"
        if n.startswith("{"):
            return f"{{{n[1:-1]} : {show(t)}}}" if t is not None else n
        return f"({n} : {show(t)})" if t is not None else n
    return " ".join(one(n, t) for n, t in names)
