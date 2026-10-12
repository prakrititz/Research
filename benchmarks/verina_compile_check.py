"""Superseded by ``benchmarks/lean_eval.py`` (one tool for every dataset). Kept so that the old command still works:

    python benchmarks/verina_compile_check.py [...]   ==   python benchmarks/lean_eval.py compile --dataset verina [...]
"""
import os
import runpy
import sys

if __name__ == "__main__":
    sys.argv[1:] = ["compile", "--dataset", "verina"] + sys.argv[1:]
    runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean_eval.py"), run_name="__main__")
