"""Run HumanEval / EvalPlus tests on a program, on any operating system.

EvalPlus' own sandbox (``evalplus.eval.untrusted_check``) enforces per-test time
limits with Unix signals (``signal.setitimer``) and memory limits with
``resource``; neither exists on Windows, where every task then ends as a
"timeout" -- the canonical solutions of the first eight problems scored 0 of 8.

This module reproduces EvalPlus' verdict semantics without those calls:

* the program runs in a **fresh interpreter process** (killed after an overall
  deadline), so a runaway program cannot hang the study;
* each test case runs on a **worker thread** with its own time limit, which is
  how a limit can be enforced without signals; after a timeout the process exits
  at once, since a thread cannot be killed;
* a test passes under the same rule as EvalPlus: exact equality, otherwise (for
  floats) ``numpy.allclose`` with ``rtol=1e-7`` and ``atol`` (1e-6 when the
  expected value is a float and no tolerance is given); HumanEval/32 uses
  EvalPlus' own oracle.

It is **not a security sandbox**: the program runs with the user's rights. Only
run programs you generated yourself. Memory is not limited.
"""

import json
import os
import pickle
import subprocess
import sys
import tempfile
import time
from typing import List, Optional, Sequence, Tuple

_DRIVER = r'''
import copy, json, pickle, sys, threading, traceback

def is_floats(x):
    import numpy as np
    if isinstance(x, float):
        return True
    if isinstance(x, (list, tuple)) and x:
        return all(isinstance(i, float) for i in x)
    if isinstance(x, np.ndarray):
        return x.dtype == np.float64 or x.dtype == np.float32
    return False

def judge(entry, out, exp, inp, atol):
    import numpy as np
    if entry == "find_zero":
        from evalplus.eval._special_oracle import _poly
        return abs(_poly(*inp, out)) <= atol
    exact = out == exp
    if atol == 0 and is_floats(exp):
        atol = 1e-6
    if not exact and atol != 0:
        if type(out) != type(exp):
            return False
        if isinstance(exp, (list, tuple)) and len(out) != len(exp):
            return False
        return bool(np.allclose(out, exp, rtol=1e-07, atol=atol))
    return bool(exact)

def main():
    with open(sys.argv[1], "rb") as fh:
        job = pickle.load(fh)
    results = []
    scope = {}
    try:
        exec(job["code"], scope)
        fn = scope[job["entry"]]
    except BaseException as e:
        print(json.dumps({"status": "fail", "details": [], "error": "load: " + repr(e)[:300]}))
        return
    for inp, exp, limit in zip(job["inputs"], job["expected"], job["limits"]):
        box = {}
        def work():
            try:
                box["out"] = fn(*copy.deepcopy(inp))
            except BaseException as e:
                box["err"] = e
        t = threading.Thread(target=work, daemon=True)
        t.start()
        t.join(limit)
        if t.is_alive():
            print(json.dumps({"status": "timeout", "details": results}))
            sys.stdout.flush()
            import os
            os._exit(0)
        ok = False
        if "err" not in box:
            try:
                ok = judge(job["entry"], box["out"], exp, inp, job["atol"])
            except BaseException:
                ok = False
        results.append(ok)
    print(json.dumps({"status": "pass" if all(results) else "fail", "details": results}))

main()
'''


def run_cases(code: str, entry: str, inputs: Sequence, expected: Sequence, limits: Sequence[float],
              atol: float, overall_timeout: float) -> Tuple[str, List[bool], str]:
    """Run one program on ``inputs``; return ``(status, per-case results, error)``."""
    with tempfile.TemporaryDirectory(prefix="fllm_he_") as workdir:
        job_path = os.path.join(workdir, "job.pkl")
        driver_path = os.path.join(workdir, "driver.py")
        with open(job_path, "wb") as fh:
            pickle.dump({"code": code, "entry": entry, "inputs": list(inputs),
                         "expected": list(expected), "limits": list(limits), "atol": atol}, fh)
        with open(driver_path, "w", encoding="utf8") as fh:
            fh.write(_DRIVER)
        try:
            done = subprocess.run([sys.executable, driver_path, job_path], cwd=workdir,
                                  capture_output=True, text=True, timeout=overall_timeout)
        except subprocess.TimeoutExpired:
            return "timeout", [], "overall deadline"
        lines = [l for l in done.stdout.strip().splitlines() if l.startswith("{")]
        if not lines:
            return "fail", [], (done.stderr or "no output").strip()[-300:]
        payload = json.loads(lines[-1])
        return payload["status"], payload.get("details", []), payload.get("error", "")
