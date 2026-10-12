"""Superseded by ``FormalLLM/lean/evaluate.py`` (the evaluator) and ``benchmarks/lean_eval.py`` (the command line), which work on
every dataset. ``python benchmarks/verina_eval.py oracle`` is ``python benchmarks/lean_eval.py reference --dataset verina``."""
import os
import runpy
import sys

if __name__ == "__main__":
    sys.argv[1:] = ["reference", "--dataset", "verina"] + [a for a in sys.argv[1:] if a != "oracle"]
    runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean_eval.py"), run_name="__main__")
