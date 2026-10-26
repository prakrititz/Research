r"""Free measure of the framework's prover: how many steps that needed a *human-proved helper lemma* the automation closes alone.

    python benchmarks/prover_ceiling.py --dataset humaneval [--only ID ...] [--out FILE]

In the paper the LLM never writes proofs: CoqHammer (cvc4, Vampire, E, Z3) discharges every obligation. Here, an obligation the
automation cannot close falls to the model as a Lean proof, and that is where trials end EXHAUSTED: in the capped measurement of
2026-10-26 a task was solved exactly when its hand-written derivation needed no helper lemma. So this script takes every certified
hand-written derivation that brings helper lemmas, removes the lemmas, and replays it through the engine: a step that still goes
through is one the automation can do alone. For a step that does not, Lean's library search is tried on its open obligation.
No model is called. The share of such tasks the automation completes is the ceiling to raise before any paid run.
"""
import argparse
import copy
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def strip_lemmas(tree):
    tree = copy.deepcopy(tree)
    count = 0
    stack = [tree]
    while stack:
        node = stack.pop()
        count += len(node.pop("lemmas", None) or [])
        stack.extend(node.get("children") or [])
    return tree, count


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", nargs="+", default=["humaneval", "classic"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--out", default="")
    ap.add_argument("--no-search", action="store_true", help="skip Lean's library search on the open obligations")
    args = ap.parse_args()
    from FormalLLM.lean import dataset as datasets
    from FormalLLM.lean.agent import LeanAgent
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession

    out = args.out or os.path.join(ROOT, "benchmarks", "results", f"prover_ceiling_{'_'.join(args.dataset)}.jsonl")
    done = {json.loads(l)["task"] for l in open(out, encoding="utf8")} if os.path.exists(out) else set()
    jobs = []
    for name in args.dataset:
        folder = os.path.join(ROOT, "exports", name)
        for task in sorted(os.listdir(folder)):
            path = os.path.join(folder, task, "derivation.json")
            if not os.path.exists(path) or task in done or (args.only and task not in args.only):
                continue
            tree, removed = strip_lemmas(json.load(open(path, encoding="utf8")))
            if removed:
                jobs.append((task, tree, removed))
    print(f"{len(jobs)} derivations that needed helper lemmas", flush=True)
    agent = LeanAgent(None)
    with LeanSession(imports=FULL_IMPORTS) as lean, open(out, "a", encoding="utf8") as handle:
        for task_id, tree, removed in jobs:
            lean.recycle()
            started = time.time()
            row = {"task": task_id, "lemmas_removed": removed}
            try:
                task = datasets.resolve(task_id).load(task_id)
                der = Derivation(task, lean, counterexamples=False)
                steps = der.apply_tree(tree)
                failing = [s for s in steps if not s.ok]
                # counted only with the full certificate: the whole term compiles, standard axioms only, every test passes
                certificate = der.certify() if (not failing and der.complete) else None
                row["automation_alone"] = bool(certificate and certificate.verified)
                row["steps_accepted"] = not failing and der.complete
                if certificate is not None and not certificate.verified:
                    row["certificate_errors"] = [e[:300] for e in certificate.errors[:2]]
                open_obs = [v for s in failing for v in s.verdicts if v.status == "UNPROVED"]
                row["failed_status"] = failing[0].status if failing else ""
                row["open_obligations"] = [v.obligation.description for v in open_obs][:4]
                row["unsolved"] = [g[:500] for v in open_obs for g in v.unsolved][:2]
                if failing and open_obs and len(failing) == 1 and not args.no_search:
                    found = []
                    for k, v in enumerate(open_obs):
                        lemma, hint = agent._library_search(der, f"search{k}", v.obligation)
                        found.append(lemma is not None)
                    row["search_closes_all"] = all(found)
                else:
                    row["search_closes_all"] = False
            except Exception as error:
                row["error"] = f"{type(error).__name__}: {error}"[:300]
                row["automation_alone"] = row["search_closes_all"] = False
            row["seconds"] = round(time.time() - started, 1)
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
            handle.flush()
            print(f"{task_id:36s} alone={row['automation_alone']!s:5s} with_search={row['search_closes_all']!s:5s} "
                  f"{row.get('failed_status', '')} {row['seconds']:6.1f}s", flush=True)


if __name__ == "__main__":
    main()
