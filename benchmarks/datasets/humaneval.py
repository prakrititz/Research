"""HumanEval / HumanEval+ (EvalPlus) access and test execution.

Protocol of the paper's Table 6: for each of the 164 problems, take the program
a system generated and run it twice -- once on the original HumanEval tests
("base") and once on EvalPlus' roughly 80x larger test set ("plus"). The table
reports how many of the 164 programs pass all tests in each setting.

This module reuses EvalPlus' own ground truth and comparison code
(``evalplus.evaluate.check_correctness``), so a pass here means exactly what a
pass means in EvalPlus. Nothing is reimplemented except the thin wrapper.

Windows note: EvalPlus' sandbox imports the Unix-only ``resource`` module. A
no-op stand-in lives in ``_shim/resource.py`` and is appended to ``sys.path``
only if ``import resource`` fails. Consequence: on Windows the *time* limit is
enforced but the *memory* limit is not. Use WSL/Linux for the full sandbox.

Data/licences: HumanEval (OpenAI, MIT) and EvalPlus (Apache-2.0) are fetched by
the ``evalplus`` package into its own cache; no dataset file is stored in this
repository.
"""
from __future__ import annotations

import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, asdict
from typing import Dict, Iterable, List, Optional

_SHIM_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_shim")


def _ensure_resource_module() -> bool:
    """Make ``import resource`` work; return True if the shim had to be used."""
    try:
        import resource  # noqa: F401
        return False
    except ImportError:
        if _SHIM_DIR not in sys.path:
            sys.path.append(_SHIM_DIR)  # appended: can never shadow a real module
        import importlib
        importlib.invalidate_caches()
        import resource  # noqa: F401
        return True


USING_RESOURCE_SHIM = _ensure_resource_module()

_BENCH_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _import_evalplus():
    """EvalPlus' four entry points, imported with the ``benchmarks`` folder stepped off ``sys.path``.

    EvalPlus needs the Hugging Face ``datasets`` library. Several scripts and tests put the
    ``benchmarks`` folder itself on ``sys.path`` and there our own ``benchmarks/datasets`` package
    answers to the name ``datasets`` -- so the import failed and everything that needs EvalPlus
    looked as if it were not installed (the pipeline tests were skipped without a word).
    """
    def norm(path):
        return os.path.normcase(os.path.abspath(path or os.curdir))

    here = norm(_BENCH_DIR)
    saved = list(sys.path)
    shadow = sys.modules.get("datasets")
    if shadow is not None and norm(getattr(shadow, "__file__", "") or "").startswith(here + os.sep):
        del sys.modules["datasets"]          # our package, imported under the library's name
    sys.path[:] = [p for p in sys.path if norm(p) != here]
    try:
        from evalplus.data import get_human_eval_plus, get_human_eval_plus_hash
        from evalplus.evaluate import check_correctness, get_groundtruth
    finally:
        sys.path[:] = saved + [p for p in sys.path if p not in saved]
    return get_human_eval_plus, get_human_eval_plus_hash, check_correctness, get_groundtruth


try:  # pragma: no cover - exercised by the tests when evalplus is installed
    get_human_eval_plus, get_human_eval_plus_hash, check_correctness, get_groundtruth = _import_evalplus()
    EVALPLUS_AVAILABLE = True
except ImportError:  # pragma: no cover
    EVALPLUS_AVAILABLE = False

NUM_PROBLEMS = 164

_problems_cache: Optional[Dict[str, dict]] = None
_groundtruth_cache: Optional[dict] = None


def _require_evalplus() -> None:
    if not EVALPLUS_AVAILABLE:
        raise RuntimeError("evalplus is not installed: run `python -m pip install --user evalplus`")


def load_problems() -> Dict[str, dict]:
    """task_id -> EvalPlus problem dict (prompt, entry_point, canonical_solution,
    base_input, plus_input, atol, contract, test). Cached."""
    global _problems_cache
    _require_evalplus()
    if _problems_cache is None:
        _problems_cache = get_human_eval_plus()
    return _problems_cache


def task_ids() -> List[str]:
    return [f"HumanEval/{i}" for i in range(NUM_PROBLEMS)]


def groundtruth() -> dict:
    """Expected outputs of the canonical solutions (EvalPlus computes and caches
    them; the first call takes ~15 s)."""
    global _groundtruth_cache
    _require_evalplus()
    if _groundtruth_cache is None:
        _groundtruth_cache = get_groundtruth(load_problems(), get_human_eval_plus_hash(), [])
    return _groundtruth_cache


def canonical_source(task_id: str) -> str:
    p = load_problems()[task_id]
    return p["prompt"] + p["canonical_solution"]


_FENCE = re.compile(r"```(?:python|py)?\s*\n(.*?)```", re.S | re.I)

#: Keys under which a model has put its program when the endpoint forces ``json_object`` replies
#: (the hosted endpoint does by default): ``{"code": "python\\ndef f(...): ..."}``.
_CODE_KEYS = ("code", "python", "solution", "function", "program", "answer", "content")

#: A first line that only names the language (``python``, ``py``, ``python3``) is not code.
_LANG_TAG = re.compile(r"\A\s*(?:python3?|py)[ \t]*\n", re.I)


def _from_json(text: str) -> Optional[str]:
    """The program inside a JSON-object reply, or None when ``text`` is not one."""
    stripped = text.strip()
    if not stripped.startswith("{"):
        return None
    try:
        obj = json.loads(stripped)
    except ValueError:
        return None
    if not isinstance(obj, dict):
        return None
    values = [obj[k] for k in _CODE_KEYS if isinstance(obj.get(k), str) and obj[k].strip()]
    if not values:                                       # unknown key: take any string value
        values = [v for v in obj.values() if isinstance(v, str) and v.strip()]
    if not values:
        return None
    return next((v for v in values if re.search(r"\bdef\s+\w+\s*\(", v)), values[0])


def extract_code(text: str) -> str:
    """The program text inside a model reply.

    Three shapes are understood, because models and endpoints differ: a JSON object whose value
    is the program (a Markdown fence inside it is opened too); a Markdown fence; or bare code.
    A leading line that only names the language (``python``) is dropped. Before this existed a
    JSON reply was run as if it were Python, a SyntaxError, and every problem was scored as failed.
    """
    inner = _from_json(text)
    code = text if inner is None else inner
    fenced = _FENCE.search(code)
    if fenced:
        code = fenced.group(1)
    return _LANG_TAG.sub("", code, count=1)


def full_source(task_id: str, text: str) -> str:
    """Turn model output into a complete program EvalPlus can run.

    Unwraps JSON replies and Markdown fences (:func:`extract_code`); if the text does not define
    the entry point (a bare function body, as in the original HumanEval completion setting) the
    problem prompt is prepended.
    """
    p = load_problems()[task_id]
    code = extract_code(text)
    if re.search(rf"^\s*def\s+{re.escape(p['entry_point'])}\s*\(", code, re.M):
        return code
    return p["prompt"] + code


@dataclass
class RunResult:
    task_id: str
    base: str                      # 'pass' | 'fail' | 'timeout'
    plus: Optional[str]            # None when plus=False
    n_base: int
    n_plus: Optional[int]
    base_failed: int
    plus_failed: Optional[int]
    seconds: float

    @property
    def base_ok(self) -> bool:
        return self.base == "pass"

    @property
    def plus_ok(self) -> Optional[bool]:
        return None if self.plus is None else self.plus == "pass"

    def as_dict(self) -> dict:
        d = asdict(self)
        d["base_ok"], d["plus_ok"] = self.base_ok, self.plus_ok
        return d


def run_tests(task_id: str, python_source: str, plus: bool = True,
              min_time_limit: float = 1.0, gt_time_limit_factor: float = 4.0) -> RunResult:
    """Run one program on one problem's tests.

    ``min_time_limit`` / ``gt_time_limit_factor`` are EvalPlus' own per-test time
    limit parameters (limit = max(min_time_limit, factor * canonical runtime)).
    ``python_source`` must be a complete program (see :func:`full_source`).

    Execution uses :mod:`exec_portable`, which reproduces EvalPlus' verdicts without
    Unix signals, so it gives the same answers on Windows and Linux.
    """
    from benchmarks.datasets.exec_portable import run_cases

    p = load_problems()[task_id]
    gt = groundtruth()[task_id]
    t0 = time.time()

    def stage(inputs, expected, times):
        limits = [max(min_time_limit, gt_time_limit_factor * t) for t in times]
        deadline = max(30.0, sum(limits) + 30.0)
        return run_cases(python_source, p["entry_point"], inputs, expected, limits,
                         p.get("atol", 0) or 0, deadline)

    b_status, b_det, _ = stage(p["base_input"], gt["base"], gt["base_time"])
    b_failed = (sum(1 for x in b_det if not x) + (len(p["base_input"]) - len(b_det))) if b_status != "pass" else 0
    p_status, p_failed = None, None
    if plus and b_status == "pass":
        p_status, p_det, _ = stage(p["plus_input"], gt["plus"], gt["plus_time"])
        p_failed = (sum(1 for x in p_det if not x) + (len(p["plus_input"]) - len(p_det))) if p_status != "pass" else 0
    elif plus:
        p_status, p_failed = b_status, len(p["plus_input"])     # a program that fails base cannot pass plus
    secs = time.time() - t0
    return RunResult(task_id, b_status, p_status, len(p["base_input"]),
                     len(p["plus_input"]) if plus else None, b_failed, p_failed, round(secs, 2))


def evaluate_solutions(solutions: Dict[str, str], plus: bool = True, workers: int = 8,
                       **limits) -> dict:
    """Table-6-style evaluation of {task_id: complete python source}.

    Tasks with no solution count as failures. Returns counts out of 164 plus the
    per-task results. ``workers`` threads each launch EvalPlus' own sandbox
    process, so this scales with CPU cores.
    """
    groundtruth()  # compute once, before the threads start
    todo = [t for t in task_ids() if t in solutions]
    with ThreadPoolExecutor(max_workers=max(1, workers)) as ex:
        results = list(ex.map(lambda t: run_tests(t, solutions[t], plus=plus, **limits), todo))
    per = {r.task_id: r for r in results}
    base_pass = sum(1 for r in results if r.base_ok)
    plus_pass = sum(1 for r in results if r.plus_ok) if plus else None
    return {
        "total": NUM_PROBLEMS,
        "attempted": len(todo),
        "humaneval_passed": base_pass,
        "evalplus_passed": plus_pass,
        "failed_base": sorted(t for t, r in per.items() if not r.base_ok),
        "failed_plus": sorted(t for t, r in per.items() if plus and not r.plus_ok),
        "per_task": per,
        "windows_resource_shim": USING_RESOURCE_SHIM,
    }


def smoke_test_canonical(plus: bool = True, workers: int = 8, limit: Optional[int] = None) -> dict:
    """Run every canonical solution through the harness. A correct harness must
    give 164/164 on HumanEval; the EvalPlus count is reported as found."""
    ids = task_ids()[:limit] if limit else task_ids()
    sols = {t: canonical_source(t) for t in ids}
    return evaluate_solutions(sols, plus=plus, workers=workers)


if __name__ == "__main__":  # python -m benchmarks.datasets.humaneval [--base-only] [--limit N]
    import argparse
    ap = argparse.ArgumentParser(description="Smoke-test the HumanEval/EvalPlus harness on canonical solutions")
    ap.add_argument("--base-only", action="store_true")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--workers", type=int, default=8)
    a = ap.parse_args()
    t0 = time.time()
    s = smoke_test_canonical(plus=not a.base_only, workers=a.workers, limit=a.limit)
    print(f"attempted {s['attempted']}/{s['total']}  "
          f"HumanEval {s['humaneval_passed']}  EvalPlus {s['evalplus_passed']}  "
          f"({time.time() - t0:.0f}s, resource shim: {s['windows_resource_shim']})")
    print("failed on base :", s["failed_base"])
    print("failed on plus :", s["failed_plus"])
