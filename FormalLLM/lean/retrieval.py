"""Worked examples for the agent's prompt: certified derivations of *other* tasks whose specifications look most like this one.

The paper gives its model a library of refined specifications (Table 8: fall-back 26.9 % -> 9.5 %). Ours is ``exports/``: the
hand-written, certified derivations. To keep a task from seeing its own answer (or a near copy from the same benchmark), the
pool is always the *other* benchmark: HumanEval and classic tasks draw on Verina, Verina tasks draw on HumanEval and classics.
Similarity is TF-IDF cosine over the identifiers and symbols of the specification.
"""
import json
import math
import os
import re
from collections import Counter
from typing import Dict, List, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
EXPORTS = os.path.join(ROOT, "exports")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.!?]*|[∀∃↔→∧∨¬≤≥<>=+\-*/%]")
# lines every Verina prelude shares (compatibility shims, the test tactic): they say nothing about the task
NOISE = re.compile(r"(?s)namespace Array.*?end Std\.HashSet|syntax \"wit_search\".*?wit_search\)\)|import Mathlib")


def _postcondition(spec: str) -> str:
    text = NOISE.sub("", spec)
    m = re.search(r"def \w+_postcond.*", text, flags=re.S)
    return (m.group(0) if m else text).strip()


class _Index:
    def __init__(self):
        self.docs: Dict[str, Tuple[str, Counter, str]] = {}      # id -> (dataset, tf, rendered example)
        self.df: Counter = Counter()
        for dataset in ("humaneval", "classic", "verina"):
            folder = os.path.join(EXPORTS, dataset)
            if not os.path.isdir(folder):
                continue
            for task in os.listdir(folder):
                spec_p, der_p = os.path.join(folder, task, "spec.lean"), os.path.join(folder, task, "derivation.json")
                if not (os.path.exists(spec_p) and os.path.exists(der_p)):
                    continue
                spec = open(spec_p, encoding="utf8").read()
                tree = json.load(open(der_p, encoding="utf8"))
                answer = json.dumps(tree, ensure_ascii=False, separators=(",", ":"))
                if len(answer) > 1600:                     # a long derivation teaches less than it costs in tokens
                    continue
                post = _postcondition(spec)
                tf = Counter(TOKEN.findall(post))
                self.docs[task] = (dataset, tf, f"Specification:\n{post}\nCertified derivation (the JSON answer format):\n{answer}")
                self.df.update(set(tf))
        self.n = max(1, len(self.docs))

    def _vec(self, tf: Counter) -> Dict[str, float]:
        v = {t: c * math.log((1 + self.n) / (1 + self.df.get(t, 0))) for t, c in tf.items()}
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {t: x / norm for t, x in v.items()}

    def nearest(self, task_id: str, spec_text: str, k: int = 2) -> List[str]:
        pool = ("humaneval", "classic") if task_id.startswith("verina") else ("verina",)
        q = self._vec(Counter(TOKEN.findall(_postcondition(spec_text))))
        scored = []
        for other, (dataset, tf, rendered) in self.docs.items():
            if other == task_id or dataset not in pool:
                continue
            v = self._vec(tf)
            scored.append((sum(q.get(t, 0.0) * x for t, x in v.items()), other, rendered))
        scored.sort(reverse=True)
        return [f"Worked example ({other}):\n{rendered}" for _, other, rendered in scored[:k]]


_INDEX = None


def examples(task_id: str, spec_text: str, k: int = 2) -> List[str]:
    global _INDEX
    if _INDEX is None:
        _INDEX = _Index()
    return _INDEX.nearest(task_id, spec_text, k)
