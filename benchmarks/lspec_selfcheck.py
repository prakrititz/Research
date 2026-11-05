"""Python-level round trip over the corpus: Lean -> tree -> L_spec -> tree must give the same tree (up to aliases that
mean the same: `ℕ`/`Nat`, `<=`/`≤`, `f <| x`/`f x`). Fast; the Lean check (``lspec_roundtrip.py``) comes after.

    python benchmarks/lspec_selfcheck.py [--show N]
"""
import argparse
import collections
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from lspec_corpus import items  # noqa: E402
from FormalLLM.dsl import lean_syntax, lspec_syntax  # noqa: E402
from FormalLLM.dsl.normal import normal  # noqa: E402

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
