"""Python-level round trip over the corpus: Lean -> tree -> L_spec -> tree must give the same tree (up to aliases that
mean the same: `ℕ`/`Nat`, `<=`/`≤`, `f <| x`/`f x`). Fast; the Lean check (``lspec_roundtrip.py``) comes after.

    python benchmarks/lspec_selfcheck.py [--show N]
"""
import argparse
import collections
import copy
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from lspec_corpus import items  # noqa: E402
from FormalLLM.dsl import ast as A, lean_syntax, lspec_syntax  # noqa: E402

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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--show", type=int, default=12)
    args = ap.parse_args()
    total, bad = collections.Counter(), collections.Counter()
    shown = 0
    for it in items():
        total[it.dataset] += 1
        tree = lean_syntax.parse(it.text)
        try:
            text = lspec_syntax.show(tree)
            back = lspec_syntax.parse(text)
            ok = normal(back) == normal(tree)
            why = "" if ok else "different tree"
        except Exception as error:
            ok, why, text = False, f"{type(error).__name__}: {error}", locals().get("text", "")
        if not ok:
            bad[it.dataset] += 1
            if shown < args.show:
                shown += 1
                print(f"--- {it.task} {it.path}: {why}\n  lean : {it.text[:220]}\n  lspec: {text[:220]}")
    for ds in total:
        print(f"{ds:10s} {total[ds] - bad[ds]}/{total[ds]} expressions round-trip")


if __name__ == "__main__":
    main()
