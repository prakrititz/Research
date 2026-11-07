"""Worked examples for the prompt: steps of other tasks' hand-written derivations whose goals look like this one, in
L_spec (the bank is ``exports/lspec_examples.json``, built by ``benchmarks/lspec_examples.py``).

A task never sees its own steps. With ``pool="cross"`` (the default) it sees only the other benchmark's: HumanEval and
classic tasks draw on Verina, Verina tasks on HumanEval and classic, so no near copy of the answer can be shown.
``pool="others"`` allows the same benchmark's other tasks (leave one out).

Similarity is TF-IDF cosine over the identifiers and symbols of the goal and of the task's postcondition in L_spec, on
both sides (a root goal only names the postcondition; its definition says what the task is about). With the law known
(the split workflow's applier), only steps with that law are shown; at most one step per task."""
import json
import math
import os
import re
from collections import Counter
from typing import Dict, List, Optional

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BANK = os.path.join(ROOT, "exports", "lspec_examples.json")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|[<>=!]=?|[+\-*/%]|\[|\]")


def postcondition(prelude: str) -> str:
    """The task's definitions other than its precondition, in L_spec: what a root goal's property means."""
    from FormalLLM.dsl import defs
    try:
        items = [i for i in defs.read(prelude) if isinstance(i, defs.Def) and not i.name.endswith("_precond")]
        return "\n\n".join(defs.show_lspec(i) for i in items)[-1500:]
    except Exception:
        return ""


def _benchmark(task_id: str) -> str:
    return "verina" if task_id.startswith("verina") else "humaneval"


class Bank:
    def __init__(self, path: str = BANK):
        self.items = json.load(open(path, encoding="utf8")) if os.path.exists(path) else []
        self.df: Counter = Counter()
        for item in self.items:
            item["tf"] = Counter(TOKEN.findall(item["goal"] + "\n" + item.get("spec", "")))
            self.df.update(set(item["tf"]))
        self.n = max(1, len(self.items))

    def _vec(self, tf: Counter) -> Dict[str, float]:
        v = {t: c * math.log((1 + self.n) / (1 + self.df.get(t, 0))) for t, c in tf.items()}
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {t: x / norm for t, x in v.items()}

    def nearest(self, task_id: str, spec: str, goal_text: str, law: Optional[str] = None, k: int = 2,
                pool: str = "cross") -> List[dict]:
        own = _benchmark(task_id)
        query = self._vec(Counter(TOKEN.findall(goal_text + "\n" + spec)))
        scored = []
        for item in self.items:
            if item["task"] == task_id or (law and item["law"] != law):
                continue
            if pool == "cross" and _benchmark(item["task"]) == own:
                continue
            scored.append((sum(query.get(t, 0.0) * x for t, x in self._vec(item["tf"]).items()), item))
        scored.sort(key=lambda s: -s[0])
        picked, tasks = [], set()
        for _, item in scored:
            if item["task"] not in tasks:
                picked.append(item)
                tasks.add(item["task"])
            if len(picked) == k:
                break
        return picked


def render(item: dict) -> str:
    """An example as the model reads it; a root step shows its task's specification (the goal only names it)."""
    spec = f"Specification:\n{item['spec']}\n" if item.get("spec") and item["path"] == "0" else ""
    return f"{spec}Goal:\n{item['goal']}\nStep: {json.dumps(item['step'], ensure_ascii=False)}"


_BANK: Optional[Bank] = None
_SPECS: Dict[str, str] = {}


def task_id_of(task) -> str:
    return os.path.basename(str(getattr(task, "directory", "")).rstrip("/\\")) or getattr(task, "name", "")


def for_prompt(task, goal_text: str, law: Optional[str] = None, k: int = 2, pool: str = "cross") -> List[str]:
    """``k`` worked examples (rendered) for ``task`` at the goal shown as ``goal_text``."""
    global _BANK
    if k <= 0:
        return []
    if _BANK is None:
        _BANK = Bank()
    task_id = task_id_of(task)
    if task_id not in _SPECS:
        _SPECS[task_id] = postcondition(task.prelude)
    return [render(i) for i in _BANK.nearest(task_id, _SPECS[task_id], goal_text, law, k, pool)]
