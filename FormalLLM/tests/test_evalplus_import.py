"""EvalPlus must be found even when the ``benchmarks`` folder is first on ``sys.path``.

Several scripts and tests put that folder on the path; our own ``benchmarks/datasets`` package then
answers to the name ``datasets`` and used to break EvalPlus' import of the Hugging Face library, so
the HumanEval pipeline tests were skipped without a word whenever the whole suite ran.
"""
import importlib.util
import os
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


@pytest.mark.skipif(importlib.util.find_spec("evalplus") is None, reason="evalplus is not installed")
def test_evalplus_is_found_with_the_benchmarks_folder_first_on_the_path():
    code = (
        "import sys\n"
        f"sys.path.insert(0, {ROOT!r})\n"
        f"sys.path.insert(0, {os.path.join(ROOT, 'benchmarks')!r})\n"
        "from benchmarks.datasets import humaneval\n"
        "print(humaneval.EVALPLUS_AVAILABLE)\n"
        "print(sys.path[0] == " + repr(os.path.join(ROOT, 'benchmarks')) + ")\n"
    )
    done = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, cwd=ROOT, timeout=60)
    assert done.stdout.split() == ["True", "True"], done.stdout + done.stderr
