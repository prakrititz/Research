"""Trees that differ only in spellings Lean reads alike: `ℕ`/`Nat`, `<=`/`≤`, `f <| x`/`f x`. The Python round trips
compare ``normal`` forms; Lean itself checks the rest (``benchmarks/lspec_equiv.py``)."""
import copy

from FormalLLM.dsl import ast as A

ALIASES = {"ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat"}
OPS = {"<=": "≤", ">=": "≥"}


def normal(node):
    node = copy.deepcopy(node)
    for n in A.walk(node):
        if isinstance(n, A.Name):
            n.id = ALIASES.get(n.id, n.id)
        if isinstance(n, A.BinOp):
            n.op = OPS.get(n.op, n.op)
    return _app(node)


def _app(node):
    if isinstance(node, A.BinOp) and node.op in ("<|", "$"):
        return A.App(_app(node.left), [_app(node.right)])
    for key, value in vars(node).items():
        if isinstance(value, A.Node):
            setattr(node, key, _app(value))
        elif isinstance(value, list):
            setattr(node, key, [_app(v) if isinstance(v, A.Node) else
                                tuple(_app(x) if isinstance(x, A.Node) else x for x in v) if isinstance(v, tuple) else v
                                for v in value])
        elif isinstance(value, tuple):
            setattr(node, key, tuple(_app(x) if isinstance(x, A.Node) else x for x in value))
    return node
