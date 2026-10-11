"""Phase 5 (step 1): do Verina's ground-truth task files compile on OUR Lean (4.34.1, Mathlib for it)?

Verina pins Lean 4.18.0 (optionally 4.24.0). We run 4.34.1. Each ``task.lean`` holds the ground-truth code, the
precondition, the postcondition and a proof; if it does not compile here, our toolchain cannot judge Verina's
tasks without a second Lean installation. One persistent Lean process imports Mathlib once and checks every task.

    python benchmarks/verina_compile_check.py [--limit N]     # writes benchmarks/results/verina/compile_check.jsonl
"""
import argparse
import json
import os
import re
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")
OUT = os.path.join(ROOT, "benchmarks", "results", "verina")


def without_proof(text):
    """The task with its proof replaced by ``sorry`` (what a refinement run needs: code, precondition, postcondition)."""
    return re.sub(r"(-- !benchmark @start proof\n).*?(\s*-- !benchmark @end proof)", r"\1  sorry\2", text, flags=re.S)


def lean_body(text):
    """task.lean without its ``import`` lines (the persistent process has imported Mathlib already)."""
    return "\n".join(line for line in text.splitlines() if not re.match(r"\s*import\s", line))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--no-proof", action="store_true", help="replace each task's proof by sorry before compiling")
    args = ap.parse_args()
    from benchmarks.lean_persistent import PersistentLean
    tasks = sorted(d for d in os.listdir(DATASET) if d.startswith("verina_"))
    if args.limit:
        tasks = tasks[:args.limit]
    os.makedirs(OUT, exist_ok=True)
    rows = []
    with PersistentLean(imports="import Mathlib", timeout_s=600) as lean:
        print(f"import Mathlib: {lean.startup_seconds:.1f} s", flush=True)
        for task in tasks:
            text = open(os.path.join(DATASET, task, "task.lean"), encoding="utf8").read()
            started = time.time()
            try:
                result = lean.raw(lean_body(without_proof(text) if args.no_proof else text))
            except Exception as error:                     # the process died: record and stop
                rows.append({"task": task, "status": "CRASH", "message": str(error)[:200], "seconds": round(time.time() - started, 1)})
                print(task, "CRASH", error, flush=True)
                break
            status = "ERROR" if result["errors"] else ("SORRY" if result["sorries"] else "CLEAN")
            rows.append({"task": task, "status": status, "errors": result["errors"][:3], "sorries": result["sorries"],
                         "seconds": round(result["seconds"], 2)})
            print(f"{task:26s} {status:6s} {result['seconds']:6.1f} s  {(result['errors'] or [''])[0][:90]}", flush=True)
    with open(os.path.join(OUT, "compile_check_noproof.jsonl" if args.no_proof else "compile_check.jsonl"), "w", encoding="utf8") as handle:
        for row in rows:
            handle.write(json.dumps(row) + "\n")
    count = {k: sum(r["status"] == k for r in rows) for k in ("CLEAN", "SORRY", "ERROR", "CRASH")}
    print(f"{len(rows)} ground-truth files on Lean 4.34.1: {count} (CLEAN = compiles with a proof; SORRY = compiles, proof is a "
          f"placeholder; ERROR = does not compile)")


if __name__ == "__main__":
    main()
