"""Phase 1: a persistent Lean process (the Lean REPL) with Mathlib imported once.

Each obligation used to start ``lake env lean`` and re-import Mathlib (about 12 s warm, more cold). The REPL
(leanprover-community/repl, built under ``~/.formalllm/repl``) imports once, keeps the environment, and checks
each theorem against it. Usage as a module::

    with PersistentLean() as lean:
        status, message, seconds = lean.check(theorem_text)

``python benchmarks/lean_persistent.py`` runs a timing demo on the stored obligations.
"""
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

HOME = os.path.join(os.path.expanduser("~"), ".formalllm")
IMPORTS = ("import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Positivity\n"
           "import Mathlib.Tactic.NormNum")


class PersistentLean:
    def __init__(self, imports: str = IMPORTS, timeout_s: float = 240.0):
        from FormalLLM.lean.session import Toolchain
        self.timeout_s = timeout_s
        self.process = Toolchain().spawn_repl()
        started = time.time()
        reply = self._ask({"cmd": imports})
        self.startup_seconds = time.time() - started
        self.env = reply["env"]

    def _ask(self, message: dict) -> dict:
        self.process.stdin.write(json.dumps(message) + "\n\n")
        self.process.stdin.flush()
        text = ""
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("the Lean REPL ended")
            if line.strip() == "" and text.strip():
                break
            text += line
        return json.loads(text)

    def check(self, theorem: str):
        """``(status, message, seconds)``; status is PROVED, or UNKNOWN with the first error line."""
        started = time.time()
        reply = self._ask({"cmd": theorem, "env": self.env})
        errors = [m for m in reply.get("messages", []) if m.get("severity") == "error"]
        sorries = reply.get("sorries")
        seconds = time.time() - started
        if errors or sorries:
            first = (errors[0]["data"] if errors else "declaration uses sorry").splitlines()[0][:200]
            return "UNKNOWN", first, seconds
        return "PROVED", "", seconds

    def raw(self, text: str) -> dict:
        """Errors and sorries separately: ``{"errors": [first lines], "sorries": n, "seconds": s}``."""
        started = time.time()
        reply = self._ask({"cmd": text, "env": self.env})
        errors = [m["data"].splitlines()[0][:200] for m in reply.get("messages", []) if m.get("severity") == "error"]
        return {"errors": errors, "sorries": len(reply.get("sorries") or []), "seconds": time.time() - started}

    def close(self):
        try:
            self.process.stdin.close()
            self.process.wait(timeout=10)
        except Exception:
            self.process.kill()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


def demo(limit: int = 12):
    path = os.path.join(ROOT, "benchmarks", "results", "lean_audit", "obligations.jsonl")
    rows = [json.loads(line) for line in open(path, encoding="utf8")][:limit]
    with PersistentLean() as lean:
        print(f"Mathlib import (once): {lean.startup_seconds:.1f} s")
        total = 0.0
        for row in rows:
            status, message, seconds = lean.check(row["lean_source"])
            total += seconds
            print(f"{row['law']:24s} {status:8s} {seconds:6.2f} s  {message}")
        print(f"{len(rows)} obligations in {total:.1f} s ({total / max(1, len(rows)):.2f} s each)")


if __name__ == "__main__":
    demo(int(sys.argv[1]) if len(sys.argv) > 1 else 12)
