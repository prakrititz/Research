"""How many of the proof obligations Z3 proves can Coq and Lean also prove?

Z3 is an automated solver; Coq and Lean check proofs with a small kernel and rely
on tactics to find them. For the arithmetic in refinement obligations the tactics
(``lia``/``nra`` in Coq, ``omega``/``nlinarith`` in Lean) can be weaker than Z3.
This script measures the gap instead of assuming it:

1. it replays the repo's hand-written, known-good derivations
   (``FormalLLM/tests/test_engine_reachability.py`` and the paper's Figure 2/9
   chains) through an engine whose backend *records* every obligation;
2. it asks each requested backend about each obligation and tabulates the answer
   and the time.

    python benchmarks/automation_gap.py --backends z3 coq lean
"""
import argparse
import importlib
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from FormalLLM.refinement import engine as engine_module                  # noqa: E402
from FormalLLM.verification.backends import Z3Backend, get_backend        # noqa: E402

DERIVATION_MODULES = ["FormalLLM.tests.test_engine_reachability"]


class Recorder:
    """Delegates to Z3 and remembers every obligation it is asked about."""
    name = "recorder"

    def __init__(self):
        self.z3 = Z3Backend()
        self.obligations = []

    def verify(self, obligation, timeout_ms=None):
        self.obligations.append(obligation)
        return self.z3.verify(obligation, timeout_ms)


def collect():
    recorder = Recorder()
    original = engine_module.get_backend
    engine_module.get_backend = lambda name=None: recorder
    try:
        for module_name in DERIVATION_MODULES:
            module = importlib.import_module(module_name)
            for name in sorted(dir(module)):
                if name.startswith("test_") and callable(getattr(module, name)):
                    fn = getattr(module, name)
                    try:
                        fn()
                    except Exception:
                        pass            # tests that expect a rejection still recorded their obligations
    finally:
        engine_module.get_backend = original
    return recorder.obligations


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--backends", nargs="+", default=["z3", "coq"])
    ap.add_argument("--timeout-ms", type=int, default=60000)
    ap.add_argument("--out", default=os.path.join(ROOT, "benchmarks", "results", "automation_gap.json"))
    args = ap.parse_args()

    obligations = collect()
    backends = {name: get_backend(name) for name in args.backends}
    rows = []
    for i, obligation in enumerate(obligations):
        row = {"index": i, "description": getattr(obligation, "description", None) or "",
               "assumptions": len(obligation.assumptions)}
        for name, backend in backends.items():
            t0 = time.time()
            status, message = backend.verify(obligation, args.timeout_ms)
            row[name] = {"status": status, "seconds": round(time.time() - t0, 3),
                         "note": message.splitlines()[0][:160] if status != "PROVED" else ""}
        rows.append(row)
        print(f"[{i + 1:3d}/{len(obligations)}] " + "  ".join(
            f"{n}={row[n]['status'][0]}({row[n]['seconds']}s)" for n in backends), flush=True)

    z3_proved = [r for r in rows if r.get("z3", {}).get("status") == "PROVED"] if "z3" in backends else rows
    print(f"\n{len(rows)} obligations recorded; Z3 proved {len(z3_proved)}.")
    for name in backends:
        if name == "z3":
            continue
        ok = sum(r[name]["status"] == "PROVED" for r in z3_proved)
        print(f"  {name}: certified {ok} of the {len(z3_proved)} that Z3 proved")
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf8") as fh:
        json.dump(rows, fh, indent=1)
    print("details ->", args.out)


if __name__ == "__main__":
    main()
