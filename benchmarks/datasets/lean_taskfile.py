"""Write a task in Verina's directory format, so Verina's tasks and ours go through the same loader, evaluator and engine.

    write_task(root, task_id, name, params, ret, description, pre, post, code, tests)

produces ``root/task_id/{task.json, description.txt, task.lean, test.json}``. The ``task.lean`` has the same
``-- !benchmark @start/@end`` regions as Verina's (import, solution_aux, precond_aux, precond, code_aux, code,
postcond_aux, postcond, proof_aux, proof), so ``benchmarks/verina_eval.py`` can score it unchanged. The proof is ``sorry``:
a task states a problem; proving a solution correct is what the refinement engine is for.
"""
import json
import os
from typing import Dict, List, Optional, Sequence, Tuple


def lean_file(name: str, params: Sequence[Tuple[str, str]], ret: str, pre: str, post: str, code: str,
              pre_aux: str = "", code_aux: str = "", post_aux: str = "", solution_aux: str = "") -> str:
    binders = " ".join(f"({n} : {t})" for n, t in params)
    args = " ".join(f"({n})" for n, _ in params)
    indent = lambda text: "\n".join(("  " + line if line.strip() else line) for line in text.strip("\n").splitlines())
    return f"""-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
{solution_aux}
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
{pre_aux}
-- !benchmark @end precond_aux

@[reducible, simp]
def {name}_precond {binders} : Prop :=
  -- !benchmark @start precond
{indent(pre)}
  -- !benchmark @end precond


-- !benchmark @start code_aux
{code_aux}
-- !benchmark @end code_aux


def {name} {binders} (h_precond : {name}_precond {args}) : {ret} :=
  -- !benchmark @start code
{indent(code)}
  -- !benchmark @end code


-- !benchmark @start postcond_aux
{post_aux}
-- !benchmark @end postcond_aux


@[reducible, simp]
def {name}_postcond {binders} (result: {ret}) (h_precond : {name}_precond {args}) :=
  -- !benchmark @start postcond
{indent(post)}
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem {name}_spec_satisfied {binders} (h_precond : {name}_precond {args}) :
    {name}_postcond {args} ({name} {args} h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
"""


def write_task(root: str, task_id: str, name: str, params: Sequence[Tuple[str, str]], ret: str, description: str,
               pre: str, post: str, code: str, tests: List[dict], pre_aux: str = "", code_aux: str = "",
               post_aux: str = "", solution_aux: str = "", metadata: Optional[dict] = None,
               specification: Optional[dict] = None) -> str:
    """``tests`` is a list of ``{"input": {param: lean literal}, "expected": value, "unexpected": [values]}``."""
    directory = os.path.join(root, task_id)
    os.makedirs(directory, exist_ok=True)
    meta = {"id": task_id,
            "signature": {"name": name, "parameters": [{"param_name": n, "param_type": t} for n, t in params],
                          "return_type": ret},
            "description_file": "./description.txt", "lean_file": "./task.lean",
            "specification": specification or {"preconditions": "", "postconditions": ""},
            "metadata": metadata or {}, "test_file": "./test.json"}
    with open(os.path.join(directory, "task.json"), "w", encoding="utf8", newline="\n") as handle:
        json.dump(meta, handle, indent=4, ensure_ascii=False)
    with open(os.path.join(directory, "description.txt"), "w", encoding="utf8", newline="\n") as handle:
        handle.write(description.strip() + "\n")
    with open(os.path.join(directory, "task.lean"), "w", encoding="utf8", newline="\n") as handle:
        handle.write(lean_file(name, params, ret, pre, post, code, pre_aux, code_aux, post_aux, solution_aux))
    with open(os.path.join(directory, "test.json"), "w", encoding="utf8", newline="\n") as handle:
        json.dump(tests, handle, indent=4, ensure_ascii=False)
    return directory
