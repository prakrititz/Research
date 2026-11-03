"""The Lean specifications of HumanEval problems, one module per range of problems (each defines ``ENTRIES``, a list of dicts for
``lean_specs.add``). ``entries()`` returns them all, in the order of the problems."""
import importlib

MODULES = ["p000_019", "p020_039", "p040_059", "p060_079", "p080_099", "p100_119", "p120_139", "p140_163"]


def entries():
    out = []
    for name in MODULES:
        try:
            module = importlib.import_module(f"benchmarks.datasets.he_lean.{name}")
        except ModuleNotFoundError as error:                  # a range not written yet
            if error.name != f"benchmarks.datasets.he_lean.{name}":
                raise
            continue
        out.extend(module.ENTRIES)
    return out
