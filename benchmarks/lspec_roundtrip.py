"""Re-certify every hand-written derivation after passing its expressions through the L_spec tooling.

    python benchmarks/lspec_roundtrip.py --dataset humaneval [--transform lean] [--only ID ...] [--chunk 15]

``--transform lean``   each expression becomes ``show(parse(text))`` (the Lean parser and printer): checks that the parser
                       reads Lean as Lean does, so that the tree is a faithful starting point
``--transform lspec``  Lean -> tree -> L_spec text -> tree -> Lean (once the L_spec surface exists)

A derivation that certified before must certify after; a failure is a bug of the tooling (or a construct it misreads),
listed with the first failed obligation. Results: ``benchmarks/results/lspec/roundtrip_<transform>_<dataset>.jsonl``
(resumable). One Lean process at a time, a fresh one per chunk."""
import argparse
import copy
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from lspec_corpus import FIELDS  # noqa: E402
from FormalLLM.dsl import lean_syntax  # noqa: E402


def transform_text(text: str, how: str) -> str:
    tree = lean_syntax.parse(text)
    if how == "lean":
        return lean_syntax.show(tree)
    if how == "lspec":
        from FormalLLM.dsl import lspec_syntax
        return lean_syntax.show(lspec_syntax.parse(lspec_syntax.show(tree)))
    raise ValueError(how)


def transform_tree(step: dict, how: str) -> dict:
    step = copy.deepcopy(step)
    for f in FIELDS.get(step["law"], ()):
        step[f] = transform_text(step[f], how)
    if step["law"] == "loop":
        step["state"] = [[v, transform_text(t, how)] for v, t in step["state"]]
        step["init"] = [transform_text(v, how) for v in step["init"]]
    for lemma in step.get("lemmas") or []:
        lemma["statement"] = transform_text(lemma["statement"], how)
    step["children"] = [transform_tree(c, how) for c in step.get("children") or []]
    return step


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--transform", default="lean", choices=["lean", "lspec"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--chunk", type=int, default=15)
    args = ap.parse_args()
    from benchmarks.datasets import lean_oracle

    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"roundtrip_{args.transform}_{args.dataset}.jsonl")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    done = set()
    if os.path.exists(out):
        done = {json.loads(line)["id"] for line in open(out, encoding="utf8") if line.strip()}
    todo = {}
    for task_id, tree in trees.items():
        if task_id in done or (args.only and task_id not in args.only):
            continue
        try:
            todo[task_id] = transform_tree(tree, args.transform)
        except Exception as error:                 # the tooling cannot read this derivation: a failure, recorded as such
            with open(out, "a", encoding="utf8") as handle:
                handle.write(json.dumps({"id": task_id, "certified": False, "transform_error": str(error)[:300]},
                                        ensure_ascii=False) + "\n")
    ids = list(todo)
    for k in range(0, len(ids), args.chunk):
        chunk = {i: todo[i] for i in ids[k:k + args.chunk]}
        rows = lean_oracle.run(None, "full", oracles=chunk)
        with open(out, "a", encoding="utf8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    print(f"{sum(r['certified'] for r in rows)} of {len(rows)} {args.dataset} derivations certified after "
          f"--transform {args.transform} ({len(trees)} derivations)")


if __name__ == "__main__":
    main()
