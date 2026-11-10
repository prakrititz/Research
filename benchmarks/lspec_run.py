"""End to end in L_spec: the model refines each task from its specification to a proved program (``LSpecAgent``), and
a task counts as solved when the derivation is complete and its certificate holds (the term compiles, no ``sorry``,
the task's tests pass). This is the number comparable to Refine4LLM's.

    python benchmarks/lspec_run.py --dataset humaneval --model gold --limit 10          # the loop itself, no model
    python benchmarks/lspec_run.py --dataset humaneval --model <config> --workflow split --max-usd 2 --paid-ok

``--model gold`` answers every goal with the hand-written derivation's step, so every task whose derivation the
prover accepts must come out SOLVED: it tests the loop, the translation both ways and the certificate, for free.

Results: ``benchmarks/results/lspec/run_<dataset>_<model>_<workflow>.jsonl``, one row per task and trial (resumable).
``--no-repair`` and ``--max-binds`` are the ablation switches for the translator's conversions and the bind rule."""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))


def row_of(task_id, trial, result, seconds, model, workflow) -> dict:
    cert = result.certificate
    return {"id": task_id, "trial": trial, "model": model, "workflow": workflow, "outcome": result.outcome,
            "verified": result.verified, "calls": len(result.calls), "retractions": result.retractions,
            "detail": result.detail, "seconds": round(seconds, 1),
            "steps": [{"goal": c.goal, "outcome": c.outcome, "law": getattr(c, "law", None), "reply": c.reply[:1500],
                       "feedback": c.feedback[:800], **({"repaired": c.note} if getattr(c, "note", "") else {})}
                      for c in result.calls],
            "certificate": None if cert is None else {"compiles": cert.compiles, "axioms": cert.axioms,
                                                      "tests": cert.tests, "passed": cert.passed,
                                                      "errors": cert.errors[:2]},
            "tree": result.derivation.to_tree() if result.derivation.complete else None,
            "timing": result.derivation.timing_report()}


def library_module(lemmas: str):
    """The lemma library as a compiled module of the Lean project (``FormalLLM/lean/library_module.py``), or ``None``."""
    from FormalLLM.lean.library_module import ensure
    return ensure(lemmas)


def check_entry(task, derivation, task_id: str, folder: str) -> dict:
    """Write the finished derivation as a self-contained Lean file (``<folder>/<task>.lean``) and return what
    ``compile_file`` needs to check it."""
    from FormalLLM.lean.session import FULL_IMPORTS
    from verify_derivations import statement_is_datasets_own
    module = library_module(derivation.lemmas)
    source, tests = derivation.source(library=module is None), task.test_commands()
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, f"{task_id}.lean")
    header = FULL_IMPORTS + (f"\nimport {module}" if module else "")
    with open(path, "w", encoding="utf8", newline="\n") as handle:
        handle.write(f"{header}\n{task.compat}\n{source}\n" + "\n".join(tests) + "\n")
    return {"file": path, "tests_expected": len(tests), "statement_regions_missing": statement_is_datasets_own(task, source)}


CHECK_FIELDS = ("verified", "exit_code", "errors", "axioms", "statement_regions_missing", "tests_true", "tests_expected",
                "seconds")


def apply_check(row: dict, check: dict) -> None:
    """The fresh-process check decides the row's outcome (stricter than the REPL's certificate)."""
    row["verified"] = check["verified"]
    row["outcome"] = "SOLVED" if check["verified"] else "UNVERIFIED"
    row.setdefault("timing", {})["file_check"] = {"seconds": check.get("seconds"), "commands": 1}
    row["file_check"] = {"file": check.get("file"), **{k: check.get(k) for k in CHECK_FIELDS}}
    row.pop("file_check_pending", None)


def finish_pending(path: str, timeout: float = 1800) -> int:
    """Compile every file a run left for later (``--file-check end``) and rewrite those rows with the verdict. Run with
    no REPL open: the REPL and a fresh process compete for the page cache over Mathlib's ~6 GB of files, and a check
    that takes 4 s alone took 20-600 s next to a grown REPL (Mac, 2026-11-08)."""
    from verify_derivations import compile_file
    if not os.path.exists(path):
        return 0
    rows = [json.loads(line) for line in open(path, encoding="utf8") if line.strip()]
    pending = [r for r in rows if r.get("file_check_pending")]
    for row in pending:
        entry = dict(row["file_check_pending"])
        if not os.path.exists(entry["file"]):
            continue
        apply_check(row, {"file": entry["file"], **compile_file(entry, timeout)})
        print(f"{row['id']:34s} {row['trial']} {row['outcome']:9s} file check {row['file_check']['seconds']}s", flush=True)
    if pending:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
        os.replace(tmp, path)
    return len(pending)


def file_check(task, derivation, task_id: str, timeout: float = 1800) -> dict:
    """The finished derivation compiled by ``lake env lean`` in a fresh process (``verify_derivations.py``): no error,
    standard axioms only, the dataset's own statement, every test true. The REPL's certificate can time out after an
    hour of obligations in one session (he_001: over 300 s in the REPL, 109 s as a file). The lemma library is
    imported from its compiled module (``library_module``) when that builds."""
    from FormalLLM.lean.session import FULL_IMPORTS
    from verify_derivations import compile_file, statement_is_datasets_own
    module = library_module(derivation.lemmas)
    source, tests = derivation.source(library=module is None), task.test_commands()
    folder = os.path.join(ROOT, "benchmarks", "results", "lspec", "verified")
    os.makedirs(folder, exist_ok=True)
    path = os.path.join(folder, f"{task_id}.lean")
    header = FULL_IMPORTS + (f"\nimport {module}" if module else "")
    with open(path, "w", encoding="utf8", newline="\n") as handle:
        handle.write(f"{header}\n{task.compat}\n{source}\n" + "\n".join(tests) + "\n")
    entry = {"file": path, "tests_expected": len(tests),
             "statement_regions_missing": statement_is_datasets_own(task, source)}
    return compile_file(entry, timeout)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--model", default="gold")
    ap.add_argument("--workflow", default="joint", choices=["joint", "split"])
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--budget", type=int, default=30, help="model calls per task")
    ap.add_argument("--attempts", type=int, default=4, help="refusals per goal before its parent step is withdrawn")
    ap.add_argument("--retractions", type=int, default=3)
    ap.add_argument("--max-binds", type=int, default=3)
    ap.add_argument("--no-repair", action="store_true")
    ap.add_argument("--lemmas", action="store_true",
                    help="prove and use helper lemmas in replies (for --model gold: the hand-written derivations bring "
                         "some; without it gold measures what the prover closes alone, the strict setting)")
    ap.add_argument("--examples", type=int, default=0, help="worked examples from other tasks in each prompt")
    ap.add_argument("--samples", type=int, default=1, help="replies per attempt; the first the prover accepts is kept")
    ap.add_argument("--pool", default="cross", choices=["cross", "others"],
                    help="examples from the other benchmark only (cross) or any other task (others)")
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--max-usd", type=float, default=None)
    ap.add_argument("--paid-ok", action="store_true")
    ap.add_argument("--trees", default=None, help="with --model gold: replay the derivation trees of this results "
                    "file instead of the hand-written ones (rebuilds that run's certificates; use with --tag)")
    ap.add_argument("--tag", default="", help="suffix of the results file (a separate file for timing or ablation runs)")
    ap.add_argument("--file-check", default="end", choices=["end", "each"],
                    help="when the fresh-process check runs: after all tasks, with the REPL closed (default; much faster "
                         "on a machine where the REPL and the check compete for memory), or after each task")
    args = ap.parse_args()

    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.lspec_agent import GoldModel, LSpecAgent
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    from FormalLLM.llm.provider import LLMBudgetExhausted
    from lspec_applier import make_model
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    if args.trees:                               # a run's own derivations, replayed by the gold model: no model calls
        saved = {r["id"]: r["tree"] for r in map(json.loads, open(args.trees, encoding="utf8")) if r.get("tree")}
        trees = {k: v for k, v in trees.items() if k in saved}
        trees.update({k: saved[k] for k in trees})
    ids = [t for t in trees if not args.only or t in args.only][:args.limit]
    gold = args.model == "gold"
    provider = None if gold else make_model(args.model, args)
    tag = (args.model.replace(":", "-") + ("_norepair" if args.no_repair else "")
           + (f"_ex{args.examples}{args.pool}" if args.examples else "") + (f"_n{args.samples}" if args.samples > 1 else "") + ("_lemmas" if args.lemmas else "") + (f"_{args.tag}" if args.tag else ""))
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"run_{args.dataset}_{tag}_{args.workflow}.jsonl")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    # each run's certificates in its own folder: gold's (strict, untagged) are the committed `verified/<task>.lean`
    folder = os.path.join(ROOT, "benchmarks", "results", "lspec", "verified")
    if not (gold and tag == "gold"):
        folder = os.path.join(folder, f"{args.dataset}_{tag}_{args.workflow}")
    done = set()
    if os.path.exists(out):
        done = {(r["id"], r["trial"]) for r in map(json.loads, open(out, encoding="utf8")) if r.get("id")}
    stopped = False
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean, open(out, "a", encoding="utf8") as handle:
        for task_id in ids:
            for trial in range(args.repeats):
                if (task_id, trial) in done:
                    continue
                agent = LSpecAgent(GoldModel(trees[task_id]) if gold else provider, args.workflow, args.budget,
                                   args.attempts, args.retractions, args.max_binds, not args.no_repair,
                                   examples=args.examples, pool=args.pool, samples=args.samples, lemmas=args.lemmas)
                started = time.time()
                try:
                    lean.recycle()
                    task = resolve(task_id).load(task_id)
                    result = agent.solve(task, lean)
                    row = row_of(task_id, trial, result, time.time() - started, args.model, args.workflow)
                    if result.derivation.complete:      # the fresh-process check decides: stricter than the REPL's
                        entry = check_entry(task, result.derivation, task_id, folder)
                        if args.file_check == "each":
                            from verify_derivations import compile_file
                            apply_check(row, {"file": entry["file"], **compile_file(entry, 1800)})
                        else:
                            row["file_check_pending"] = entry
                            row["outcome"] = "CERTIFIED" if row["verified"] else row["outcome"]
                except LLMBudgetExhausted as error:  # no row: the task was cut off by money, a rerun with more resumes it
                    print(f"{task_id:34s} {trial} stopped: {error}", flush=True)
                    stopped = True
                    break
                except Exception as error:
                    row = {"id": task_id, "trial": trial, "model": args.model, "workflow": args.workflow,
                           "outcome": "ERROR", "verified": False, "detail": f"{type(error).__name__}: {str(error)[:300]}",
                           "seconds": round(time.time() - started, 1)}
                handle.write(json.dumps(row, ensure_ascii=False) + "\n")
                handle.flush()
                print(f"{task_id:34s} {trial} {row['outcome']:9s} verified={row['verified']!s:5s} "
                      f"calls={row.get('calls', 0):2d} {row['seconds']:6.1f}s {row.get('detail', '')[:80]}", flush=True)
                if row["outcome"] == "NETWORK":
                    print("the endpoint stopped serving: stopping (finished trials are kept; rerun to resume)")
                    stopped = True
                    break
            if stopped:
                break
    if finish_pending(out):                       # the REPL is closed now: the fresh-process checks run fast
        print("fresh-process checks done", flush=True)
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    solved = {r["id"] for r in rows if r.get("verified") and not r.get("file_check_pending")}
    print(f"{args.dataset} {args.model} {args.workflow}: {len(solved)}/{len({r['id'] for r in rows})} tasks solved "
          f"(verified certificate); {sum(r['outcome'] == 'ERROR' for r in rows)} errors")


if __name__ == "__main__":
    main()
