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


LIBRARY_MODULE = "LeanEnv.RefineLib"
_BUILT: dict = {}


def library_module(lemmas: str):
    """The engine's lemma library compiled once into a module of the Lean project (``LeanEnv/RefineLib.lean``, built
    by ``lake build``; rebuilt only when the library text changes), so each task's file imports it instead of
    elaborating ~140k characters again (~80 s per task on the Windows PC). Lean's kernel checks the module when it is
    built, and ``#print axioms`` follows dependencies across modules, so the check is as strict. ``None`` if the build
    fails: the file then carries the library text as before."""
    import subprocess
    from FormalLLM.lean.session import FULL_IMPORTS, Toolchain, short_path
    text = f"{FULL_IMPORTS}\n{lemmas}\n"
    key = hash(text)
    if key in _BUILT:
        return _BUILT[key]
    tool = Toolchain()
    package = LIBRARY_MODULE.split(".")[0]
    lakefile = os.path.join(tool.project, "lakefile.toml")
    lakefile_text = open(lakefile, encoding="utf8").read() if os.path.exists(lakefile) else ""
    if f'name = "{package}"' not in lakefile_text and os.path.exists(lakefile):
        # a Lean project made before the module existed has no library target to build it in (this Mac's): add one
        with open(lakefile, "a", encoding="utf8", newline="\n") as handle:
            handle.write(f'\n[[lean_lib]]\nname = "{package}"\n')
    path = os.path.join(tool.project, *LIBRARY_MODULE.split(".")) + ".lean"       # LeanEnv/RefineLib.lean
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        old = open(path, encoding="utf8").read() if os.path.exists(path) else None
        if old != text:                               # unchanged text keeps lake's trace: no rebuild
            with open(path, "w", encoding="utf8", newline="\n") as handle:
                handle.write(text)
    except OSError as error:
        print(f"the library module could not be written ({error}); files carry the library text", flush=True)
        _BUILT[key] = None
        return None
    try:
        done = subprocess.run([tool.lake, "build", LIBRARY_MODULE], cwd=short_path(tool.project), env=tool.env(),
                              capture_output=True, text=True, encoding="utf8", timeout=3600)
        _BUILT[key] = LIBRARY_MODULE if done.returncode == 0 else None
        if done.returncode != 0:
            print("the library module did not build; files carry the library text:",
                  ((done.stdout or "") + (done.stderr or ""))[-300:], flush=True)
    except (subprocess.TimeoutExpired, OSError) as error:
        print(f"the library module did not build ({error}); files carry the library text", flush=True)
        _BUILT[key] = None
    return _BUILT[key]


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
    ap.add_argument("--tag", default="", help="suffix of the results file (a separate file for timing or ablation runs)")
    args = ap.parse_args()

    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.lspec_agent import GoldModel, LSpecAgent
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    from lspec_applier import make_model
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    ids = [t for t in trees if not args.only or t in args.only][:args.limit]
    gold = args.model == "gold"
    provider = None if gold else make_model(args.model, args)
    tag = (args.model.replace(":", "-") + ("_norepair" if args.no_repair else "")
           + (f"_ex{args.examples}{args.pool}" if args.examples else "") + (f"_n{args.samples}" if args.samples > 1 else "") + ("_lemmas" if args.lemmas else "") + (f"_{args.tag}" if args.tag else ""))
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"run_{args.dataset}_{tag}_{args.workflow}.jsonl")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    done = set()
    if os.path.exists(out):
        done = {(r["id"], r["trial"]) for r in map(json.loads, open(out, encoding="utf8")) if r.get("id")}
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
                    check = file_check(task, result.derivation, task_id) if result.derivation.complete else None
                    row = row_of(task_id, trial, result, time.time() - started, args.model, args.workflow)
                    if check is not None:                 # the fresh-process check decides: stricter than the REPL's
                        row["verified"] = check["verified"]
                        row["outcome"] = "SOLVED" if check["verified"] else "UNVERIFIED"
                        row.setdefault("timing", {})["file_check"] = {"seconds": check.get("seconds"), "commands": 1}
                        row["file_check"] = {k: check.get(k) for k in ("verified", "exit_code", "errors", "axioms",
                                                                        "statement_regions_missing", "tests_true",
                                                                        "tests_expected", "seconds")}
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
                    return
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    solved = {r["id"] for r in rows if r.get("verified")}
    print(f"{args.dataset} {args.model} {args.workflow}: {len(solved)}/{len({r['id'] for r in rows})} tasks solved "
          f"(verified certificate); {sum(r['outcome'] == 'ERROR' for r in rows)} errors")


if __name__ == "__main__":
    main()
