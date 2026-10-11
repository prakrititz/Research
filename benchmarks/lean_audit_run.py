"""Phase 2 (step 2): run Lean over the 180 distinct obligations collected from the stored successful derivations.

Z3 accepted every one of them (that is how the steps were kept); Coq's tactics failed on some. For each obligation the
persistent Lean process answers PROVED or UNKNOWN (with the first error line) within ``--timeout`` seconds; a check that
runs longer is killed and the process restarted (``TIMEOUT``). Output: ``lean_audit/lean_verdicts.jsonl`` and a summary.

    python benchmarks/lean_audit_run.py [--timeout 60] [--limit N]
"""
import argparse
import collections
import json
import os
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "benchmarks", "results", "lean_audit")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    from benchmarks.lean_persistent import IMPORTS, PersistentLean
    from FormalLLM.verification.backends.lean_backend import IMPORTS as BACKEND_IMPORTS
    rows = [json.loads(line) for line in open(os.path.join(OUT, "obligations.jsonl"), encoding="utf8")]
    rows = rows[:args.limit] if args.limit else rows
    lean = PersistentLean(imports=BACKEND_IMPORTS)
    print(f"Lean ready ({lean.startup_seconds:.1f} s)", flush=True)
    verdicts, restarts = [], 0
    for index, row in enumerate(rows):
        box = {}

        def work():
            try:
                box["result"] = lean.check(row["lean_source"])
            except Exception as error:
                box["error"] = str(error)
        thread = threading.Thread(target=work, daemon=True)
        started = time.time()
        thread.start()
        thread.join(args.timeout)
        if thread.is_alive() or "error" in box:
            lean.process.kill()
            lean.close()
            lean = PersistentLean(imports=BACKEND_IMPORTS)
            restarts += 1
            status, message, seconds = "TIMEOUT", "no answer within %.0f s" % args.timeout, time.time() - started
        else:
            status, message, seconds = box["result"]
        verdicts.append({"key": row["key"], "law": row["law"], "derivations": row["derivations"],
                         "coq_failed_in": row["coq_failed_in"], "lean": status, "message": message,
                         "seconds": round(seconds, 2)})
        if (index + 1) % 20 == 0:
            print(f"  {index + 1}/{len(rows)}", dict(collections.Counter(v['lean'] for v in verdicts)), flush=True)
    lean.close()
    with open(os.path.join(OUT, "lean_verdicts.jsonl"), "w", encoding="utf8") as handle:
        for verdict in verdicts:
            handle.write(json.dumps(verdict) + "\n")
    by = collections.Counter(v["lean"] for v in verdicts)
    weighted = collections.Counter()
    for v in verdicts:
        weighted[v["lean"]] += v["derivations"]
    summary = {"distinct": len(verdicts), "lean": dict(by), "weighted_by_derivations": dict(weighted), "restarts": restarts,
               "median_seconds": sorted(v["seconds"] for v in verdicts)[len(verdicts) // 2],
               "lean_unproved_by_law": dict(collections.Counter(v["law"] for v in verdicts if v["lean"] != "PROVED")),
               "coq_failed_distinct": sum(v["coq_failed_in"] > 0 for v in verdicts)}
    json.dump(summary, open(os.path.join(OUT, "lean_summary.json"), "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
