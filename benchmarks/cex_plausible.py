"""Phase 3, second attempt: Lean's own random tester (``plausible``) as the counterexample source.

``cex_by_testing.py`` measured a small-input grid search: it found a counterexample for only 24% of the obligations Z3 refuted.
Lean ships a proper property tester (Plausible: random generation, shrinking, readable output). This script replays the same
stored runs, keeps every obligation Z3 refuted, prints each as a Lean theorem whose proof is ``plausible``, and asks the
persistent Lean process. Outcomes: ``FOUND`` (a counter-example is reported), ``NONE`` (it gave up or the statement is not
testable), ``ERROR`` (the statement did not elaborate).

    python benchmarks/cex_plausible.py [--per-file N] [--timeout S] [--recollect]
        # -> benchmarks/results/lean_audit/cex_plausible.json

First attempt: 165 of 794 found, 629 ``ERROR`` -- "Failed to create a `testable` instance". The cause is not the statement but
Lean's instance-synthesis size limit (``synthInstance.maxSize``, default 128): a conjunction of five or more parts exceeds it.
With the limits raised (``OPTIONS`` below; 2048 was not enough for the longest statements, 100000 is) the same obligations are
testable, but the random generator then often "gives up": it cannot produce values that satisfy equality hypotheses such as
``q * d + r = n``, which an SMT solver solves directly. Plausible has no sampler for ``ℝ``/``ℚ``, so
real-valued statements stay untestable (20 of the 794). The collected obligations are cached in ``cex_items.json``.
"""
import argparse
import collections
import glob
import json
import os
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "benchmarks", "results", "lean_audit")
OPTIONS = "set_option synthInstance.maxSize 100000 in\nset_option synthInstance.maxHeartbeats 0 in\n"
IMPORTS = ("import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Positivity\n"
           "import Mathlib.Tactic.NormNum\nimport Plausible")


def collect(per_file):
    from benchmarks.cases import CASES
    from benchmarks.lean_audit_collect import rebuild
    from FormalLLM.verification.backends import Z3Backend
    from FormalLLM.verification.backends import get_backend
    from FormalLLM.lspec.lean_translator import obligation_to_lean
    cases = {c["id"]: c for c in CASES}
    failed, original = [], Z3Backend.verify

    def recording(self, obligation, timeout_ms=None):
        status, message = original(self, obligation, timeout_ms)
        if status == "FAILED":
            failed.append(obligation)
        return status, message
    Z3Backend.verify = recording
    files = (glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/cases_D1-intdiv_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v6_relaxed_noassist_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v6_strict_assist_*.jsonl"))
             + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/cases_A4-impossible_*.jsonl")))
    for path in files:
        count = 0
        for line in open(path, encoding="utf8"):
            if not line.strip() or count >= per_file:
                continue
            row = json.loads(line)
            if not row.get("raw_responses"):
                continue
            count += 1
            try:
                rebuild(row, cases)
            except Exception:
                pass
    Z3Backend.verify = original
    seen, out = set(), []
    for ob in failed:
        key = repr((ob.assumptions, ob.goal))
        if key in seen:
            continue
        seen.add(key)
        try:
            header, _sorts, _parts = obligation_to_lean(ob, name="cex")
        except Exception:
            continue
        out.append({"description": getattr(ob, "description", "")[:60], "lean": header.rstrip() + " plausible\n"})
    return out, len(failed)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--per-file", type=int, default=3)
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--recollect", action="store_true", help="replay the stored runs again instead of using cex_items.json")
    args = ap.parse_args()
    from benchmarks.lean_persistent import PersistentLean
    cache = os.path.join(OUT, "cex_items.json")
    if os.path.exists(cache) and not args.recollect:
        saved = json.load(open(cache, encoding="utf8"))
        items, total = saved["items"], saved["z3_refutations"]
    else:
        items, total = collect(args.per_file)
        os.makedirs(OUT, exist_ok=True)
        json.dump({"z3_refutations": total, "items": items}, open(cache, "w", encoding="utf8"))
    print(f"{total} Z3 refutations, {len(items)} distinct and translatable to Lean", flush=True)
    lean = PersistentLean(imports=IMPORTS)
    rows, restarts = [], 0
    for index, item in enumerate(items):
        box = {}

        def work():
            try:
                box["r"] = lean._ask({"cmd": OPTIONS + item["lean"], "env": lean.env})
            except Exception as error:
                box["e"] = str(error)
        started = time.time()
        thread = threading.Thread(target=work, daemon=True)
        thread.start()
        thread.join(args.timeout)
        if thread.is_alive() or "e" in box:
            lean.process.kill()
            lean.close()
            lean = PersistentLean(imports=IMPORTS)
            restarts += 1
            status, detail = "TIMEOUT", ""
        else:
            texts = [m["data"] for m in box["r"].get("messages", []) if m["severity"] == "error"]
            joined = "\n".join(texts)
            if "Found a counter-example" in joined:
                status, detail = "FOUND", joined.split("counter-example!", 1)[1].strip().splitlines()[0:4]
            elif texts:
                status, detail = ("NONE" if ("Gave up" in joined or "gave up" in joined or "Unable to" in joined) else "ERROR"), joined[:400]
            else:
                status, detail = "PROVED_UNEXPECTED", ""
        rows.append({"description": item["description"], "status": status, "seconds": round(time.time() - started, 2),
                     "sort": "real" if "ℝ" in item["lean"] else "integer",
                     "detail": detail, "lean": item["lean"]})
        if (index + 1) % 100 == 0:
            print(f"  {index + 1}/{len(items)}", dict(collections.Counter(r['status'] for r in rows)), flush=True)
    lean.close()
    counts = collections.Counter(r["status"] for r in rows)
    summary = {"z3_refutations": total, "distinct_translatable": len(items), "plausible": dict(counts), "restarts": restarts,
               "found_share": round(counts["FOUND"] / max(1, len(items)), 3),
               "median_seconds": sorted(r["seconds"] for r in rows)[len(rows) // 2] if rows else None,
               "by_sort": {sort: dict(collections.Counter(r["status"] for r in rows if r["sort"] == sort))
                           for sort in ("integer", "real")},
               "errors_sample": [r["detail"] for r in rows if r["status"] == "ERROR"][:4]}
    os.makedirs(OUT, exist_ok=True)
    json.dump({"summary": summary, "rows": rows}, open(os.path.join(OUT, "cex_plausible.json"), "w", encoding="utf8"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
