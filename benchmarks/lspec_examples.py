"""The bank of worked examples: every step of every hand-written derivation, as the model would see and write it
(the goal in L_spec, the step in L_spec), for retrieval into the prompt (``FormalLLM/dsl/examples.py``).

    python benchmarks/lspec_examples.py            # -> exports/lspec_examples.json (no Lean, no model)

Helper lemmas are left out of the shown step (the model never writes them). Retrieval never shows a task its own
steps, and by default draws only on the other benchmark (HumanEval and classic tasks on Verina, Verina on the others)."""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.dsl import steps  # noqa: E402


def main():
    from FormalLLM.dsl.examples import postcondition
    from lspec_equiv import collect
    from lspec_steps import walk
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))
    bank, failed = [], 0
    for dataset, tasks in trees.items():
        for task_id, tree in tasks.items():
            try:
                task, derivation, _ = collect(task_id, tree)
                spec = postcondition(task.prelude)
                for path, node, sub, state in walk(derivation.root, tree):
                    scope = [n for n, _ in node.goal.ctx] + [n for n, _ in node.goal.hyps]
                    gold = {k: v for k, v in sub.items() if k not in ("children", "lemmas")}
                    bank.append({"task": task_id, "dataset": dataset, "path": path, "law": gold["law"],
                                 "goal": steps.goal_text(steps.goal_to_lspec(node.goal, state)),
                                 "step": steps.from_engine(gold, scope), "spec": spec})
            except Exception as error:
                failed += 1
                print(f"{task_id}: {type(error).__name__}: {str(error)[:150]}")
    out = os.path.join(ROOT, "exports", "lspec_examples.json")
    json.dump(bank, open(out, "w", encoding="utf8"), ensure_ascii=False, indent=0)
    print(f"{len(bank)} steps from {len({b['task'] for b in bank})} tasks -> {out}; {failed} tasks failed")


if __name__ == "__main__":
    main()
