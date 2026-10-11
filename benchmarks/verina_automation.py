"""Phase 6 floor: with the GROUND-TRUTH code, how many Verina specs does a plain tactic cascade prove with no model?

Verina's proof task asks a model for the proof of ``f_spec_satisfied`` (the code meets the postcondition). Refinement builds
that proof step by step, so the number to beat is what automation alone proves. For every task the proof region is replaced by
a fixed cascade and the file is compiled with a heartbeat limit (deterministic, no wall-clock kill needed):

    unfold <f> <f>_postcond ...; first | simp_all | grind | omega | decide | (simp; omega) | aesop

    python benchmarks/verina_automation.py     # writes benchmarks/results/verina/automation_scores.jsonl
"""
import json
import os
import re
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")
OUT = os.path.join(ROOT, "benchmarks", "results", "verina")
PROOF = re.compile(r"(-- !benchmark @start proof\n).*?(\s*-- !benchmark @end proof)", re.S)
CASCADE = ("  set_option maxHeartbeats 400000 in\n"
           "  first\n"
           "    | (unfold {f} {f}_postcond; simp_all; done)\n"
           "    | (unfold {f} {f}_postcond; grind)\n"
           "    | (unfold {f} {f}_postcond; omega)\n"
           "    | (unfold {f} {f}_postcond; simp_all; omega)\n"
           "    | (unfold {f} {f}_postcond; simp_all; grind)\n"
           "    | (unfold {f} {f}_postcond; aesop)\n"
           "    | decide")


def main():
    from benchmarks.lean_persistent import PersistentLean
    tasks = sorted(d for d in os.listdir(DATASET) if d.startswith("verina_"))
    rows = []
    with PersistentLean(imports="import Mathlib", timeout_s=900) as lean:
        print(f"import Mathlib: {lean.startup_seconds:.1f} s", flush=True)
        for task in tasks:
            tl = open(os.path.join(DATASET, task, "task.lean"), encoding="utf8").read()
            f = json.load(open(os.path.join(DATASET, task, "task.json"), encoding="utf8"))["signature"]["name"]
            body = "\n".join(l for l in tl.splitlines() if not re.match(r"\s*import\s", l))
            body = PROOF.sub(lambda m: m.group(1) + CASCADE.format(f=f) + m.group(2), body)
            started = time.time()
            try:
                result = lean.raw(body)
            except Exception as error:
                rows.append({"task": task, "status": "CRASH", "message": str(error)[:100]})
                print(task, "CRASH", flush=True)
                break
            status = "ERROR_IN_DEFS" if any("Unknown" in e for e in result["errors"][:1]) and False else \
                ("PROVED" if not result["errors"] and not result["sorries"] else "NOT_PROVED")
            rows.append({"task": task, "status": status, "errors": result["errors"][:2], "seconds": round(time.time() - started, 1)})
            print(f"{task:24s} {status:10s} {time.time() - started:6.1f}s {(result['errors'] or [''])[0][:60]}", flush=True)
    with open(os.path.join(OUT, "automation_scores.jsonl"), "w", encoding="utf8") as handle:
        for row in rows:
            handle.write(json.dumps(row) + "\n")
    proved = sum(r["status"] == "PROVED" for r in rows)
    print(f"{proved} of {len(rows)} specs proved by the cascade alone (ground-truth code, no model)")


if __name__ == "__main__":
    main()
