r"""Run the Lean agent on tasks, one record per trial, scored per problem; replay stored trials without a model.

    python benchmarks/lean_agent_run.py run --config ornith --library lean_specs --tasks he_060_sum_to_n he_100_make_a_pile --repeats 3
    python benchmarks/lean_agent_run.py run --config gpt-oss-120b-low --library verina --tasks verina_basic_5 --repeats 5
    python benchmarks/lean_agent_run.py summarize benchmarks/results/lean_agent/<file>.jsonl
    python benchmarks/lean_agent_run.py replay benchmarks/results/lean_agent/<file>.jsonl      # no model, no network

NOT run by the setup of 2026-10-08: it needs a model, and the hosted endpoint was down. Everything here is tested with a
scripted model (``FormalLLM/tests/test_lean_agent_run.py``).

The protocol is the post-meeting one (doc 22): each task is tried ``--repeats`` times; a trial is **verified** when the agent
finishes the derivation *and* the certificate holds (the whole term compiles, ``#print axioms`` has no ``sorryAx``, every test of the
task passes); a task is **solved at threshold t** when the fraction of its valid trials that are verified is at least t. A trial the
endpoint cut off (HTTP 403 bandwidth limit, no connection) is **NETWORK**, left out of the fraction, never counted as a failure.
Every record keeps the model's raw replies, so ``replay`` re-derives each trial deterministically and checks the stored outcome.
"""
import argparse
import collections
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "benchmarks", "results", "lean_agent")
LIBRARIES = {"lean_specs": os.path.join(ROOT, "benchmarks", "datasets", "lean_specs"),
             "verina": os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")}
THRESHOLDS = (0.2, 0.4, 0.5, 0.6, 0.8, 1.0)


def jsonl(path):
    return [json.loads(line) for line in open(path, encoding="utf8") if line.strip()] if os.path.exists(path) else []


def record(task_id, trial, result, seconds, config):
    certificate = result.certificate
    return {
        "task": task_id, "trial": trial, "config": config, "outcome": result.outcome, "verified": result.verified,
        "calls": len(result.calls), "retractions": result.retractions, "detail": result.detail, "seconds": round(seconds, 1),
        "call_outcomes": [c.outcome for c in result.calls],
        "replies": [c.reply for c in result.calls],                       # raw: ``replay`` needs nothing else
        "feedback": [c.feedback[:400] for c in result.calls if c.feedback],
        "laws": result.derivation.laws_used, "helper_lemmas": [h.name for h in result.derivation.helpers],
        "certificate": None if certificate is None else {
            "compiles": certificate.compiles, "axioms": certificate.axioms, "tests": certificate.tests,
            "passed": certificate.passed, "errors": certificate.errors[:2]},
        "tree": result.derivation.to_tree() if result.derivation.complete else None,
        "lean_seconds": round(result.derivation.lean_seconds, 1),
    }


def run(args):
    from benchmarks import run_bench
    from FormalLLM.lean.agent import LeanAgent
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import LeanTask
    library = LIBRARIES[args.library]
    tasks = args.tasks or sorted(d for d in os.listdir(library) if os.path.isdir(os.path.join(library, d)))
    os.makedirs(OUT, exist_ok=True)
    path = os.path.join(OUT, args.out or f"{args.library}_{args.config}.jsonl")
    done = {(r["task"], r["trial"]) for r in jsonl(path)}
    cfg = run_bench.CONFIGS[args.config]
    provider = run_bench.make_provider(cfg, args.temperature, args.timeout)
    if cfg["kind"] == "ollama" and not args.free_text:
        provider.response_format = "json"                                  # the reply is one JSON object
    agent = LeanAgent(provider, max_calls=args.budget, attempts_per_goal=args.attempts, retractions=args.retractions)
    with LeanSession(imports=args.imports) as lean, open(path, "a", encoding="utf8") as handle:
        print(f"run: {len(tasks)} tasks x {args.repeats} trials, {args.config}, writing {path}", flush=True)
        for task_id in tasks:
            task = LeanTask.from_dir(os.path.join(library, task_id))
            for trial in range(args.repeats):
                if (task_id, trial) in done:
                    continue
                started = time.time()
                result = agent.solve(task, lean)
                row = record(task_id, trial, result, time.time() - started, args.config)
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
                handle.flush()
                print(f"{task_id:30s} trial {trial}  {result.outcome:9s} verified={result.verified!s:5s} calls={row['calls']:2d} "
                      f"{row['seconds']:6.1f}s", flush=True)
                if result.outcome == "NETWORK":
                    print("the endpoint stopped serving; stopping (re-run later: finished trials are kept)", flush=True)
                    return


def solved_table(rows):
    """Per-problem scoring: (task -> (valid trials, verified)), thresholds, mean rate."""
    by_task = collections.defaultdict(list)
    for row in rows:
        by_task[row["task"]].append(row)
    table = {}
    for task, trials in by_task.items():
        valid = [t for t in trials if t["outcome"] != "NETWORK"]
        table[task] = (len(valid), sum(bool(t["verified"]) for t in valid), len(trials) - len(valid))
    return table


def summarize(path):
    rows = jsonl(path)
    table = solved_table(rows)
    lines = [f"{path}: {len(rows)} trials on {len(table)} tasks", "",
             "| Task | Valid trials | Verified | Rate | " + " | ".join(f">= {int(t * 100)}%" for t in THRESHOLDS) + " | Network |",
             "|---|---|---|---|" + "---|" * (len(THRESHOLDS) + 1)]
    counts = {t: 0 for t in THRESHOLDS}
    rates = []
    for task in sorted(table):
        valid, verified, network = table[task]
        rate = verified / valid if valid else 0.0
        rates.append(rate)
        marks = []
        for t in THRESHOLDS:
            ok = valid > 0 and verified > 0 and rate >= t - 1e-9
            counts[t] += ok
            marks.append("yes" if ok else "-")
        lines.append(f"| {task} | {valid} | {verified} | {rate:.2f} | " + " | ".join(marks) + f" | {network} |")
    n = len(table)
    lines += ["", f"Solved at threshold: " + ", ".join(f">= {int(t * 100)}%: {counts[t]}/{n}" for t in THRESHOLDS),
              f"Mean per-problem verified rate: {sum(rates) / n:.3f}" if n else "", ""]
    text = "\n".join(lines)
    print(text)
    return text


def replay(path):
    """Re-derive every stored trial from its stored replies (no model) and check that the outcome is reproduced."""
    from FormalLLM.lean.agent import LeanAgent
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import LeanTask
    from FormalLLM.llm.provider import LLMProvider

    class Stored(LLMProvider):
        def __init__(self, replies):
            self.replies = list(replies)

        def generate(self, prompt, max_tokens=None):
            return self.replies.pop(0) if self.replies else ""

    rows = jsonl(path)
    mismatches = 0
    with LeanSession() as lean:
        for row in rows:
            if row["outcome"] == "NETWORK":
                continue
            library = LIBRARIES["verina"] if row["task"].startswith("verina_") else LIBRARIES["lean_specs"]
            task = LeanTask.from_dir(os.path.join(library, row["task"]))
            result = LeanAgent(Stored(row["replies"]), max_calls=len(row["replies"]) + 1).solve(task, lean)
            same = (result.outcome, result.verified) == (row["outcome"], row["verified"])
            mismatches += not same
            print(f"{row['task']:30s} trial {row['trial']}  stored {row['outcome']}/{row['verified']}  replayed "
                  f"{result.outcome}/{result.verified}  {'same' if same else 'DIFFERENT'}", flush=True)
    print(f"{len(rows) - mismatches} of {len(rows)} trials reproduced")
    return mismatches


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    r = sub.add_parser("run")
    r.add_argument("--config", default="gpt-oss-120b-low")
    r.add_argument("--library", choices=list(LIBRARIES), default="lean_specs")
    r.add_argument("--tasks", nargs="*")
    r.add_argument("--repeats", type=int, default=3)
    r.add_argument("--budget", type=int, default=30, help="model calls per trial")
    r.add_argument("--attempts", type=int, default=4, help="attempts per goal before its parent step is withdrawn")
    r.add_argument("--retractions", type=int, default=3)
    r.add_argument("--temperature", type=float, default=0.2)
    r.add_argument("--timeout", type=int, default=900)
    r.add_argument("--imports", default=None, help="Lean imports; default: the small set; use 'import Mathlib' for tasks that need it")
    r.add_argument("--free-text", action="store_true", help="do not force a JSON object from Ollama models")
    r.add_argument("--out", default=None)
    s = sub.add_parser("summarize")
    s.add_argument("file")
    p = sub.add_parser("replay")
    p.add_argument("file")
    args = ap.parse_args()
    if args.command == "run":
        from FormalLLM.lean.session import DEFAULT_IMPORTS
        args.imports = args.imports or DEFAULT_IMPORTS
        run(args)
    elif args.command == "summarize":
        summarize(args.file)
    else:
        sys.exit(1 if replay(args.file) else 0)


if __name__ == "__main__":
    main()
