"""Superseded by ``benchmarks/lean_baseline.py`` (``--dataset verina|humaneval``). Kept so that the old command works."""
import os
import runpy
import sys

if __name__ == "__main__":
    if "--dataset" not in sys.argv:
        sys.argv += ["--dataset", "verina"]
    runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean_baseline.py"), run_name="__main__")
