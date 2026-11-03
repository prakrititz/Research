r"""How well does the Lean engine catch wrong steps? Mutation testing of the hand-written derivations.

Each oracle derivation (``benchmarks/datasets/lean_oracle.py``) is correct. Take it, change one expression in one step (add 1
to a number, ``+`` to ``-``, ``<`` to ``≤``, ``&&`` to ``||``, ``=`` to ``≠``...), and give the mutant to the engine. A mutant ends as

* **ill-formed**: Lean could not read it (cannot happen for these operators except by accident);
* **unproved**: the engine rejected the step; with a **counter-example** when ``plausible`` found values that break it;
* **survived, certified**: the engine accepted it, the whole term compiled with no ``sorry`` and every test passed (the mutation
  did not change the meaning, or the specification allows both);
* **survived, failing tests**: accepted and certified but some test fails. This must never happen if specification and engine
  are right: the program is proved to meet the specification yet disagrees with HumanEval's expected output, so the
  specification is weaker than the problem. Every such case is listed.

    python benchmarks/lean_mutation_feedback.py [--only ID ...] [--limit N]   # -> benchmarks/results/lean_specs/mutation_feedback.json
"""
import argparse
import collections
import copy
import json
import os
import re
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
RESULTS = os.path.join(ROOT, "benchmarks", "results", "lean_specs")

#: (name, pattern, replacement): applied to the first match in a field
OPERATORS = [
    ("number+1", re.compile(r"(?<![\w.])(\d+)(?![\w.])"), lambda m: str(int(m.group(1)) + 1)),
    ("plus->minus", re.compile(r" \+ "), lambda m: " - "),
    ("lt->le", re.compile(r" < "), lambda m: " ≤ "),
    ("le->lt", re.compile(r" ≤ "), lambda m: " < "),
    ("ge->gt", re.compile(r" ≥ "), lambda m: " > "),
    ("and->or", re.compile(r" && "), lambda m: " || "),
    ("eq->ne", re.compile(r" = "), lambda m: " ≠ "),
]
FIELDS = {"term": ["expr"], "cases": ["cond"], "bind": ["prop"], "loop": ["init", "invariant", "guard", "result", "variant"]}


def mutants(tree, path=()):
    """All single mutations of the tree: (description, mutated tree)."""
    law = tree.get("law")
    for field in FIELDS.get(law, []):
        value = tree[field]
        values = value if isinstance(value, list) else [value]
        for index, text in enumerate(values):
            for name, pattern, replace in OPERATORS:
                match = pattern.search(text)
                if not match:
                    continue
                changed = text[:match.start()] + replace(match) + text[match.end():]
                if changed == text:
                    continue
                copy_tree = copy.deepcopy(tree)
                target = copy_tree[field]
                if isinstance(target, list):
                    target[index] = changed
                else:
                    copy_tree[field] = changed
                yield f"{'/'.join(map(str, path)) or 'root'}:{law}.{field}:{name}", copy_tree
    for k, child in enumerate(tree.get("children", [])):
        for description, mutated in mutants(child, path + (k,)):
            copy_tree = copy.deepcopy(tree)
            copy_tree["children"][k] = mutated
            yield description, copy_tree


def classify(derivation, steps):
    bad = [s for s in steps if not s.ok]
    if bad:
        step = bad[0]
        if step.status == "ill_formed":
            return "ill_formed", None
        found = [v.counterexample for v in step.verdicts if not v.proved and v.counterexample]
        return ("unproved_with_counterexample", found[0]) if found else ("unproved", None)
    if not derivation.complete:
        return "incomplete", None
    certificate = derivation.certify()
    if not certificate.compiles or not certificate.sound:
        return "survived_uncertified", "; ".join(certificate.errors)[:200]
    if certificate.tests and certificate.passed != certificate.tests:
        return "survived_failing_tests", f"{certificate.passed}/{certificate.tests} tests pass"
    return "survived_certified", None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--limit", type=int, default=0, help="at most this many mutants per derivation (0 = all)")
    args = ap.parse_args()
    from benchmarks.datasets.lean_oracle import LIBRARY, ORACLES
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import LeanTask
    rows, counts = [], collections.Counter()
    started = time.time()
    with LeanSession() as lean:
        for task_id, tree in ORACLES.items():
            if args.only and task_id not in args.only:
                continue
            task = LeanTask.from_dir(os.path.join(LIBRARY, task_id))
            local = collections.Counter()
            options = list(mutants(tree))
            if args.limit:
                step = max(1, len(options) // args.limit)
                options = options[::step][:args.limit]
            for description, mutated in options:
                try:
                    derivation = Derivation(task, lean)
                    steps = derivation.apply_tree(mutated)
                    outcome, detail = classify(derivation, steps)
                except Exception as error:               # a mutation that breaks the harness itself is reported, not hidden
                    outcome, detail = "harness_error", str(error)[:200]
                counts[outcome] += 1
                local[outcome] += 1
                rows.append({"task": task_id, "mutation": description, "outcome": outcome, "detail": detail})
                if outcome in ("survived_failing_tests", "harness_error"):
                    print(f"  !! {task_id} {description}: {outcome} {detail}", flush=True)
            print(f"{task_id:30s} {len(options):3d} mutants  " + "  ".join(f"{k}={v}" for k, v in sorted(local.items())),
                  flush=True)
    total = sum(counts.values())
    killed = counts["unproved"] + counts["unproved_with_counterexample"] + counts["ill_formed"]
    summary = {"mutants": total, "outcomes": dict(counts), "killed": killed,
               "kill_rate": round(killed / total, 3) if total else None,
               "counterexample_share_of_killed": round(counts["unproved_with_counterexample"] / killed, 3) if killed else None,
               "seconds": round(time.time() - started, 1)}
    os.makedirs(RESULTS, exist_ok=True)
    with open(os.path.join(RESULTS, "mutation_feedback.json"), "w", encoding="utf8") as handle:
        json.dump({"summary": summary, "rows": rows}, handle, indent=1, ensure_ascii=False)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
