r"""Free framework check: send each certified hand-written derivation through the *agent* as if a model had answered with it.

    python benchmarks/pipeline_check.py --dataset humaneval classic        # -> benchmarks/results/pipeline_check_<names>.jsonl
    python benchmarks/pipeline_check.py --dataset verina

No model is called. A scripted provider replies once with the known-correct derivation (``exports/<dataset>/<id>/derivation.json``),
and the agent runs exactly as in a benchmark: prompt building (with every fix of ``FORMALLLM_FIXES`` on), reply checks, the engine's
obligations, the certificate. Every task must come out SOLVED in one call. A task that does not is a framework fault: a correct
answer the pipeline refuses would make a model fail on it too, however good the model is.
"""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", nargs="+", default=["humaneval", "classic", "verina"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--out", default="")
    args = ap.parse_args()
    from FormalLLM.lean import dataset as datasets
    from FormalLLM.lean.agent import LeanAgent
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    from FormalLLM.llm.provider import LLMProvider

    class Scripted(LLMProvider):
        def __init__(self, replies):
            self.replies = list(replies)
            self.prompts = []

        def generate(self, prompt, max_tokens=None):
            self.prompts.append(prompt)
            return self.replies.pop(0) if self.replies else ""

    out = args.out or os.path.join(ROOT, "benchmarks", "results", f"pipeline_check_{'_'.join(args.dataset)}.jsonl")
    done = set()
    if os.path.exists(out):
        done = {json.loads(l)["task"] for l in open(out, encoding="utf8") if l.strip()}
    jobs = []
    for name in args.dataset:
        folder = os.path.join(ROOT, "exports", name)
        for task in sorted(os.listdir(folder)):
            path = os.path.join(folder, task, "derivation.json")
            if os.path.exists(path) and task not in done and (not args.only or task in args.only):
                jobs.append((task, path))
    print(f"{len(jobs)} derivations to check ({len(done)} already done)", flush=True)
    with LeanSession(imports=FULL_IMPORTS) as lean, open(out, "a", encoding="utf8") as handle:
        for task_id, path in jobs:
            started = time.time()
            answer = open(path, encoding="utf8").read()
            provider = Scripted([answer])
            try:
                task = datasets.resolve(task_id).load(task_id)
                result = LeanAgent(provider, max_calls=2).solve(task, lean)
                outcome, verified, detail = result.outcome, result.verified, result.detail
                feedback = [c.feedback[:600] for c in result.calls if c.outcome != "applied"]
            except Exception as error:                     # a crash is a framework fault too
                outcome, verified, detail, feedback = "CRASH", False, f"{type(error).__name__}: {error}"[:400], []
            row = {"task": task_id, "outcome": outcome, "verified": verified, "calls": len(provider.prompts),
                   "detail": detail, "feedback": feedback, "prompt_chars": max((len(p) for p in provider.prompts), default=0),
                   "seconds": round(time.time() - started, 1)}
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
            handle.flush()
            print(f"{task_id:36s} {outcome:9s} verified={verified!s:5s} {row['seconds']:6.1f}s {detail[:80]}", flush=True)


if __name__ == "__main__":
    main()
