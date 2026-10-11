"""Phase 5 (step 2): a Verina code-task evaluator on our Lean (4.34.1), validated first on the ground truth.

For a task, a candidate is the Lean code that replaces the ``-- !benchmark @start code`` region of ``task.lean``
(with the proof replaced by ``sorry``). It is scored in two ways, both inside one persistent Lean process:

* **compiles**: the file has no error;
* **tests**: every case of ``test.json`` is evaluated with ``#eval (f inputs proof == expected)``; the case passes
  when it prints ``true``. Cases whose precondition cannot be discharged by ``simp``/``decide`` are reported as
  ``precondition-unproved`` and counted separately, never as a pass.

``oracle`` mode runs the ground-truth code of every task: it measures the harness itself (how many tasks it can score at
all), not any model. ``python benchmarks/verina_eval.py oracle [--limit N]``.
"""
import json
import os
import re
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from FormalLLM.lean.task import lean_string
DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")
OUT = os.path.join(ROOT, "benchmarks", "results", "verina")
CODE = re.compile(r"(-- !benchmark @start code\n)(.*?)(\n\s*-- !benchmark @end code)", re.S)
PROOF = re.compile(r"(-- !benchmark @start proof\n).*?(\s*-- !benchmark @end proof)", re.S)


def render(value, type_text):
    """A JSON value as a Lean literal for a value of type ``type_text``."""
    t = type_text.strip()
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return f"({value})" if value < 0 else str(value)
    if isinstance(value, str):
        # the dataset stores non-String expected values as Lean literals ("some 2", "#[1, 2]"): use them as written
        return lean_string(value) if t == "String" else value
    if isinstance(value, list):
        inner = re.match(r"(?:Array|List)\s+(.*)", t)
        elem = inner.group(1) if inner else ""
        body = ", ".join(render(v, elem) for v in value)
        return f"#[{body}]" if t.startswith("Array") else f"[{body}]"
    if value is None:
        return "none"
    return json.dumps(value, ensure_ascii=False)


AUX = re.compile(r"(-- !benchmark @start code_aux\n)(.*?)(\n?-- !benchmark @end code_aux)", re.S)


def candidate(task_lean: str, code: str, aux: str = "") -> str:
    """task.lean with ``code`` as the body of the code region (and ``aux`` as helper definitions before it), proof = ``sorry``."""
    text = CODE.sub(lambda m: m.group(1) + code + m.group(3), task_lean)
    if aux.strip():
        text = AUX.sub(lambda m: m.group(1) + aux + "\n" + m.group(3), text)
    text = PROOF.sub(lambda m: m.group(1) + "  sorry" + m.group(2), text)
    return "\n".join(line for line in text.splitlines() if not re.match(r"\s*import\s", line))


def ground_truth_code(task_lean: str) -> str:
    return CODE.search(task_lean).group(2)


def tests_for(task_dir: str):
    meta = json.load(open(os.path.join(task_dir, "task.json"), encoding="utf8"))
    cases = json.load(open(os.path.join(task_dir, "test.json"), encoding="utf8"))
    name = meta["signature"]["name"]
    types = {p["param_name"]: p["param_type"] for p in meta["signature"]["parameters"]}
    ret = meta["signature"]["return_type"]
    lines = []
    for case in cases:
        args = " ".join(f"({case['input'][p]})" for p in types)
        proof = f"(by first | trivial | (norm_num [{name}_precond]; done) | (simp [{name}_precond]; done) | decide | omega | native_decide)"
        lines.append(f"#eval (({name} {args} {proof}) == {render(case['expected'], ret)})")
    return lines


def score(lean, task_id: str, code=None, aux: str = ""):
    task_dir = os.path.join(DATASET, task_id)
    task_lean = open(os.path.join(task_dir, "task.lean"), encoding="utf8").read()
    source = candidate(task_lean, code if code is not None else ground_truth_code(task_lean), aux)
    started = time.time()
    base = lean.raw(source)
    result = {"task": task_id, "compiles": not base["errors"], "errors": base["errors"][:2], "tests": 0, "passed": 0,
              "unproved": 0, "seconds": 0.0}
    if base["errors"]:
        result["seconds"] = round(time.time() - started, 2)
        return result
    tests = tests_for(task_dir)
    result["tests"] = len(tests)
    # the definitions are already in the environment of this REPL command only if we re-send them: send the file once
    # with all #eval lines appended, then read one message per #eval
    reply = lean._ask({"cmd": source + "\n" + "\n".join(tests), "env": lean.env})
    infos = [m for m in reply.get("messages", []) if m.get("severity") == "info"]
    errors = [m for m in reply.get("messages", []) if m.get("severity") == "error"]
    passed = sum(1 for m in infos if m.get("data", "").strip() == "true")
    result["passed"] = passed
    result["unproved"] = len(errors)            # an #eval with an unprovable precondition argument is an error
    result["seconds"] = round(time.time() - started, 2)
    return result


def main():
    from benchmarks.lean_persistent import PersistentLean
    mode = sys.argv[1] if len(sys.argv) > 1 else "oracle"
    limit = None
    if "--limit" in sys.argv:
        limit = int(sys.argv[sys.argv.index("--limit") + 1])
    tasks = sorted(d for d in os.listdir(DATASET) if d.startswith("verina_"))
    tasks = tasks[:limit] if limit else tasks
    os.makedirs(OUT, exist_ok=True)
    rows = []
    with PersistentLean(imports="import Mathlib", timeout_s=600) as lean:
        print(f"import Mathlib: {lean.startup_seconds:.1f} s", flush=True)
        for task in tasks:
            row = score(lean, task)
            rows.append(row)
            print(f"{task:24s} compiles={row['compiles']!s:5s} tests {row['passed']}/{row['tests']} unproved-pre {row['unproved']} "
                  f"{row['seconds']:5.1f}s {(row['errors'] or [''])[0][:60]}", flush=True)
    with open(os.path.join(OUT, f"{mode}_scores.jsonl"), "w", encoding="utf8") as handle:
        for row in rows:
            handle.write(json.dumps(row) + "\n")
    comp = sum(r["compiles"] for r in rows)
    full = sum(r["compiles"] and r["tests"] and r["passed"] == r["tests"] for r in rows)
    print(f"{len(rows)} tasks: {comp} compile, {full} pass every test case")


if __name__ == "__main__":
    main()
