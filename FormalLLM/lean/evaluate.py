"""One evaluator for every dataset: the same checks on a Verina task and on a HumanEval task.

A task directory (:mod:`FormalLLM.lean.dataset`) holds a Lean file whose ``code`` region is a reference solution and whose ``proof``
region is not needed. This module does two things with it, in one :class:`~FormalLLM.lean.session.LeanSession`:

``score_code(lean, task, code)``
    Put ``code`` (and optional helper definitions) into the ``code`` region, compile, then run every case of ``test.json``.
    This is how a model's plain answer (the *direct baseline*) and the dataset's own reference solution are scored.

``validate_task(lean, task)``
    Check the *specification* against the data, the four checks of ``Reading Material/24``: (1) the file compiles with its
    reference solution; (2) the reference passes every test; (3) the postcondition accepts the expected output of every test;
    (4) the postcondition rejects every ``unexpected`` output. Verina's ``test.json`` carries ``unexpected`` lists like ours, so the
    same four numbers are available for both datasets.

Nothing here names a dataset.
"""
import time
from typing import Any, Dict, Optional

from FormalLLM.lean.task import AUX, CODE, PROOF, LeanTask, precondition_proof, render, same_expr, strip_imports

HEARTBEATS = "set_option maxHeartbeats 2000000 in\n"


def task_source(task: LeanTask) -> str:
    with open(f"{task.directory}/task.lean", encoding="utf8") as handle:
        return handle.read()


def ground_truth_code(task_lean: str) -> str:
    return CODE.search(task_lean).group(2)


def candidate_source(task_lean: str, code: Optional[str] = None, aux: str = "", compat: str = "") -> str:
    """``task.lean`` with ``code`` as the body of the code region (``aux``: helper definitions before it), the proof replaced
    by ``sorry`` and the imports removed (the session has imported Mathlib already)."""
    text = CODE.sub(lambda m: m.group(1) + (ground_truth_code(task_lean) if code is None else code) + m.group(3), task_lean)
    if aux.strip():
        text = AUX.sub(lambda m: m.group(1) + aux + "\n" + m.group(3), text)
    text = PROOF.sub(lambda m: m.group(1) + "  sorry" + m.group(2), text)
    return (compat + "\n" if compat.strip() else "") + strip_imports(text)


def score_code(lean, task: LeanTask, code: Optional[str] = None, aux: str = "", load_timeout: float = 240,
               test_timeout: float = 90) -> Dict[str, Any]:
    """Compile the task with ``code`` and run its tests. ``code=None`` scores the dataset's reference solution.

    ``unproved`` counts tests that did not run (an ``#eval`` whose precondition argument could not be proved is an error)."""
    started = time.time()
    source = candidate_source(task_source(task), code, aux, task.compat)
    reply, env = lean.load(source, timeout=load_timeout)
    result = {"task": task.id, "compiles": env is not None, "errors": [e[:400] for e in reply.errors[:2]],
              "tests": 0, "passed": 0, "unproved": 0, "seconds": 0.0}
    if env is None:
        if reply.timed_out:
            result["errors"] = ["timeout while compiling"]
        result["seconds"] = round(time.time() - started, 2)
        return result
    commands = task.test_commands()
    result["tests"] = len(commands)
    for command in commands:
        answer = lean.run(command, timeout=test_timeout, env=env)
        if answer.errors or not answer.infos:
            result["unproved"] += 1
        elif answer.infos[0].strip() == "true":
            result["passed"] += 1
    result["seconds"] = round(time.time() - started, 2)
    return result


def solved(result: Dict[str, Any]) -> bool:
    """Compiles and passes every test (and there is at least one test)."""
    return bool(result["compiles"] and result["tests"] and result["passed"] == result["tests"])


def validate_task(lean, task: LeanTask, reference_mode: str = "equal", permissive: bool = False) -> Dict[str, Any]:
    """The four specification checks on one task (see the module docstring).

    ``reference_mode="spec"``: the reference's output must satisfy the postcondition (for a specification with several right
    answers) instead of being equal to the expected value. ``permissive``: the specification may accept an "unexpected" output
    (a dictionary in another order); it is only recorded.
    """
    row = {"id": task.id, "compiles": False, "tests": len(task.tests), "reference_passes": 0, "accepts_expected": 0,
           "rejects_wrong": 0, "wrong_total": 0, "undecidable": 0, "errors": [], "failures": [],
           "permissive": permissive, "reference_mode": reference_mode}
    # the reference code with the proof replaced by ``sorry``: a specification is validated, not the dataset's proofs (which also
    # break across Lean versions without saying anything about the task)
    reply, env = lean.load(candidate_source(task_source(task), None, "", task.compat), timeout=240)
    row["compiles"] = env is not None
    if env is None:
        row["errors"] = [e[:300] for e in (reply.errors or ["timeout"])[:2]]
        return row
    proof = precondition_proof(task.pre_name)

    def value(command: str) -> Optional[str]:
        answer = lean.run(HEARTBEATS + command, timeout=120, env=env)
        if answer.errors or not answer.infos:
            if len(row["errors"]) < 3:
                row["errors"].append((answer.errors or ["no output"])[0][:200])
            return None
        return answer.infos[0].strip()

    def fail(kind: str, args: str, detail: str):
        if len(row["failures"]) < 4:
            row["failures"].append({"kind": kind, "input": args[:160], "value": detail[:100]})

    for case in task.tests:
        args = task.call_args(case)
        want = render(case["expected"], task.ret)
        if reference_mode == "spec":
            ran = value(f"#eval decide ({task.post_name} {args} ({task.name} {args} {proof}) {proof})")
        else:
            ran = value(f"#eval {same_expr(task.ret, f'({task.name} {args} {proof})', want)}")
        row["reference_passes"] += ran == "true"
        if ran != "true":
            fail("reference", args, f"expected {want}" + ("" if ran else " (did not run)"))
        accepted = value(f"#eval decide ({task.post_name} {args} ({want}) {proof})")
        row["accepts_expected"] += accepted == "true"
        row["undecidable"] += accepted is None
        if accepted != "true":
            fail("accept", args, f"expected {want}" + ("" if accepted else " (spec did not run)"))
        for wrong in case.get("unexpected", []):
            row["wrong_total"] += 1
            shown = value(f"#eval decide ({task.post_name} {args} ({render(wrong, task.ret)}) {proof})")
            row["rejects_wrong"] += shown == "false"
            if shown != "false":
                fail("reject", args, f"wrong {render(wrong, task.ret)}" + ("" if shown else " (spec did not run)"))
    return row


def validation_ok(row: Dict[str, Any]) -> bool:
    """All four checks hold (a permissive row may accept a reordered "wrong" output)."""
    return bool(row["compiles"] and row["reference_passes"] == row["tests"] == row["accepts_expected"]
                and row["undecidable"] == 0
                and (row["rejects_wrong"] == row["wrong_total"] or row["permissive"]))
