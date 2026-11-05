"""The syntax tree shared by both surfaces: the Lean subset the derivations are written in (``lean_syntax.py``) and the
L_spec the model writes (``lspec_syntax.py``). A step goes L_spec text -> tree -> Lean text; the corpus check goes the
other way, Lean text -> tree -> L_spec text -> tree -> Lean text, and Lean proves the two Lean texts equal."""
from dataclasses import dataclass, field
from typing import List, Optional, Tuple


class Node:
    pass


@dataclass
class Name(Node):
    id: str                                      # a variable, or a global (`List.range`, `Nat.Prime`, `isPal`)


@dataclass
class Num(Node):
    text: str                                    # `3`, `2.5`


@dataclass
class Char(Node):
    text: str                                    # the source text between the quotes (escapes kept)


@dataclass
class Str(Node):
    text: str                                    # likewise


@dataclass
class App(Node):
    fn: Node
    args: List[Node]


@dataclass
class Dot(Node):
    obj: Node
    field: str                                   # `x.length`, `p.1`


@dataclass
class Index(Node):
    obj: Node
    idx: Node
    kind: str = "!"                              # `a[i]!`, `a[i]?`, `a[i]`


@dataclass
class BinOp(Node):
    op: str
    left: Node
    right: Node


@dataclass
class UnOp(Node):
    op: str                                      # `¬`, `-`, `!`, `↑`
    arg: Node


@dataclass
class Binder(Node):
    kind: str                                    # `∀`, `∃`, `fun`
    vars: List[Tuple[str, Optional[Node]]]       # names with their types (None: inferred)
    bound: Optional[Tuple[str, Node]]            # `∀ x ∈ l, ...` / `∀ i < n, ...`
    body: Node
    pattern: Optional[Node] = None               # unused: a pattern is a binder named `<pat>` (its "type" is the pattern)


@dataclass
class If(Node):
    cond: Node
    then: Node
    other: Node
    hyp: Optional[str] = None                    # `if h : c then ...`


@dataclass
class Let(Node):
    name: str
    type: Optional[Node]
    value: Node
    body: Node
    params: List[Tuple[str, Optional[Node]]] = field(default_factory=list)   # `let f (x : T) := ...`


@dataclass
class Tuple_(Node):
    items: List[Node]


@dataclass
class ListLit(Node):
    items: List[Node]
    array: bool = False                          # `#[...]`


@dataclass
class Anon(Node):
    items: List[Node]                            # `⟨a, b⟩`


@dataclass
class Ascribe(Node):
    expr: Node
    type: Node


@dataclass
class Abs(Node):
    arg: Node
    kind: str = "|"                              # `|x|`, `⌊x⌋` (floor), `⌈x⌉` (ceiling)


@dataclass
class Match(Node):
    scrutinees: List[Node]
    arms: List[Tuple[List[Node], Node]] = field(default_factory=list)


def walk(node: Node):
    """Every node of the tree, parents first."""
    yield node
    for value in vars(node).values():
        items = value if isinstance(value, list) else [value]
        for item in items:
            if isinstance(item, tuple):
                for part in item:
                    if isinstance(part, Node):
                        yield from walk(part)
                    elif isinstance(part, list):
                        for p in part:
                            if isinstance(p, Node):
                                yield from walk(p)
            elif isinstance(item, Node):
                yield from walk(item)
