"""The L_spec coverage corpus: every Lean expression the hand-written derivations contain (``exports/all_derivations.json``),
with where it comes from. What the model will write in L_spec instead of Lean is exactly this set: values, loop state
(types and initial values), invariants, guards, variants, results, case conditions, bound propositions and helper-lemma
statements. Proofs are left out: in the L_spec workflow the model states lemmas and the prover proves them.

    python benchmarks/lspec_corpus.py            # parse coverage of the Lean subset, and the constructs that fail
"""
import collections
import json
import os
import sys
from dataclasses import dataclass
from typing import Iterator

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from FormalLLM.dsl import lean_syntax  # noqa: E402

FIELDS = {"term": ("expr",), "loop": ("invariant", "guard", "variant", "result"), "cases": ("cond",),
          "bind": ("prop", "type")}


@dataclass
class Item:
    dataset: str
    task: str
    path: str                     # `0.1.loop.invariant`: the step's position in the tree, then the field
    kind: str                     # expr | type | prop | lemma
    text: str


def items(path: str = os.path.join(ROOT, "exports", "all_derivations.json")) -> Iterator[Item]:
    data = json.load(open(path, encoding="utf8"))
    for dataset, tasks in data.items():
        for task, tree in tasks.items():
            yield from _step(dataset, task, tree, "0")


def _step(dataset, task, step, at) -> Iterator[Item]:
    law = step["law"]
    for f in FIELDS.get(law, ()):
        kind = "type" if f == "type" else "prop" if f in ("invariant", "guard", "cond", "prop") else "expr"
        yield Item(dataset, task, f"{at}.{law}.{f}", kind, step[f])
    if law == "loop":
        for k, (var, typ) in enumerate(step["state"]):
            yield Item(dataset, task, f"{at}.loop.state.{k}", "type", typ)
        for k, value in enumerate(step["init"]):
            yield Item(dataset, task, f"{at}.loop.init.{k}", "expr", value)
    for k, lemma in enumerate(step.get("lemmas") or []):
        yield Item(dataset, task, f"{at}.{law}.lemma.{k}", "lemma", lemma["statement"])
    for k, child in enumerate(step.get("children") or []):
        yield from _step(dataset, task, child, f"{at}.{k}")


def main():
    total, failed = collections.Counter(), collections.Counter()
    reasons, examples, bad_tasks = collections.Counter(), {}, collections.defaultdict(set)
    tasks = collections.defaultdict(set)
    for it in items():
        total[it.dataset] += 1
        tasks[it.dataset].add(it.task)
        try:
            lean_syntax.parse(it.text)
        except Exception as error:                       # Unsupported, or a bug of the parser: both are listed
            failed[it.dataset] += 1
            reason = f"{type(error).__name__}: {error}"[:80]
            reasons[reason] += 1
            examples.setdefault(reason, f"{it.task} {it.path}: {it.text[:160]}")
            bad_tasks[it.dataset].add(it.task)
    for ds in total:
        print(f"{ds:10s} expressions {total[ds]:5d}  parsed {total[ds] - failed[ds]:5d} "
              f"({100 * (total[ds] - failed[ds]) / total[ds]:.1f}%)  tasks fully parsed "
              f"{len(tasks[ds]) - len(bad_tasks[ds])}/{len(tasks[ds])}")
    for reason, n in reasons.most_common(40):
        print(f"{n:4d}  {reason}\n      {examples[reason]}")


if __name__ == "__main__":
    main()
