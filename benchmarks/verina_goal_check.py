r"""How many of Verina's 189 tasks can the Lean engine even start on? (Phase 6 readiness, no model.)

For each task: read it (``LeanTask.from_dir``), load the lemma library and the task's own definitions (precondition,
postcondition, helper definitions: *without* the reference code and proof) into Lean 4.34.1, and open the root goal. A task that
fails here cannot be refined whatever the model does: the cause is the Lean version (Verina pins 4.18/4.24; ours is 4.34.1), a library
name that changed, or a definition the engine cuts out wrongly.

    python benchmarks/verina_goal_check.py [--imports full|default]      # -> benchmarks/results/verina/goal_check.json
"""
import argparse
import collections
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")
OUT = os.path.join(ROOT, "benchmarks", "results", "verina")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--imports", choices=["default", "full"], default="full")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import DEFAULT_IMPORTS, FULL_IMPORTS, LeanSession
    from FormalLLM.lean.task import LeanTask
    tasks = sorted(d for d in os.listdir(DATASET) if d.startswith("verina_"))
    tasks = tasks[:args.limit] if args.limit else tasks
    rows, started = [], time.time()
    with LeanSession(imports=FULL_IMPORTS if args.imports == "full" else DEFAULT_IMPORTS, startup_timeout=1200) as lean:
        for task_id in tasks:
            row = {"task": task_id, "family": task_id.split("_")[1], "reads": False, "loads": False, "error": ""}
            rows.append(row)
            try:
                task = LeanTask.from_dir(os.path.join(DATASET, task_id))
                row.update(reads=True, params=len(task.params), tests=len(task.tests), ret=task.ret,
                           trivial_precondition=f"def {task.pre_name}" in task.prelude and
                           task.prelude.split(f"def {task.pre_name}", 1)[1].split("def ", 1)[0].split(":=", 1)[1].strip().split("\n")[0].strip() == "True")
                Derivation(task, lean)._environment()
                row["loads"] = True
            except Exception as error:
                row["error"] = str(error)[:200].replace("\n", " ")
            print(f"{task_id:26s} reads={row['reads']!s:5s} loads={row['loads']!s:5s} {row['error'][:90]}", flush=True)
    by = collections.defaultdict(lambda: [0, 0])
    for r in rows:
        by[r["family"]][0] += r["loads"]
        by[r["family"]][1] += 1
    errors = collections.Counter(r["error"][:70] for r in rows if r["error"])
    summary = {"tasks": len(rows), "reads": sum(r["reads"] for r in rows), "loads": sum(r["loads"] for r in rows),
               "by_family": {k: f"{a}/{b}" for k, (a, b) in by.items()},
               "trivial_precondition_among_loaded": sum(1 for r in rows if r["loads"] and r.get("trivial_precondition")),
               "common_errors": errors.most_common(6), "seconds": round(time.time() - started, 1)}
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "goal_check.json"), "w", encoding="utf8") as handle:
        json.dump({"summary": summary, "rows": rows}, handle, indent=1, ensure_ascii=False)
    print(json.dumps(summary, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
