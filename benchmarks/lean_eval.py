r"""The same checks on any dataset: ``--dataset verina`` or ``--dataset humaneval`` (or ``classic``, ``lean_specs``).

    python benchmarks/lean_eval.py list      --dataset verina
    python benchmarks/lean_eval.py validate  --dataset humaneval [--only ID ...] [--limit N]
    python benchmarks/lean_eval.py reference --dataset verina    [--only ID ...] [--limit N]
    python benchmarks/lean_eval.py compile   --dataset verina [--no-proof]
    python benchmarks/lean_eval.py goals     --dataset humaneval
    python benchmarks/lean_eval.py automation --dataset verina
    python benchmarks/lean_eval.py oracles   --dataset humaneval [--only ID ...]
    python benchmarks/lean_eval.py summary   --dataset verina

``validate``   the four specification checks (compiles; reference passes every test; the postcondition accepts the expected
               output; it rejects every ``unexpected`` output)               -> results/<dataset>/validation.json
``reference``  score the dataset's own reference solution on its tests: which tasks the harness can score at all (the set a direct
               baseline is allowed to use, so a model's failure is the model's)  -> results/<dataset>/reference_scores.jsonl

``compile``    does each task file compile on this Lean (with its proof, or with the proof replaced by ``sorry``)
``goals``      can the engine open the root goal of each task (the task's own definitions load, without the reference code)
``automation`` with the reference code given, how many postconditions a fixed tactic cascade proves (the floor refinement must beat)
``oracles``    run the hand-written derivations of the dataset through the engine and certify them

Results are resumable (finished tasks are kept; ``--redo`` starts over). One Lean process, Mathlib imported once.
"""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def read_jsonl(path):
    return [json.loads(line) for line in open(path, encoding="utf8") if line.strip()] if os.path.exists(path) else []


def select(ds, args):
    ids = ds.ids()
    if args.only:
        ids = [i for i in ids if i in set(args.only)]
    return ids[:args.limit] if args.limit else ids


def cmd_list(ds, args):
    ids = select(ds, args)
    for i in ids:
        task = ds.load(i)
        print(f"{i:44s} {ds.family(i):10s} {len(task.params)} params  {len(task.tests):2d} tests  {task.ret}")
    print(f"{len(ids)} tasks in {ds.name} ({ds.root})")
    return 0


def cmd_validate(ds, args):
    from FormalLLM.lean.evaluate import validate_task, validation_ok
    from FormalLLM.lean.session import LeanSession
    path = ds.result_path("validation.jsonl")
    if args.redo and os.path.exists(path):
        os.remove(path)
    done = {r["id"] for r in read_jsonl(path)}
    todo = [i for i in select(ds, args) if i not in done]
    print(f"validate {ds.name}: {len(todo)} to do, {len(done)} already in {path}", flush=True)
    with LeanSession(imports=args.imports, startup_timeout=1800) as lean, open(path, "a", encoding="utf8") as out:
        print(f"imports ready in {lean.startup_seconds:.0f} s", flush=True)
        for i in todo:
            started = time.time()
            row = validate_task(lean, ds.load(i))
            row["family"] = ds.family(i)
            row["seconds"] = round(time.time() - started, 1)
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
            out.flush()
            status = "ok" if validation_ok(row) else ("DOES NOT COMPILE" if not row["compiles"] else "CHECK")
            print(f"{i:44s} {status:16s} tests {row['tests']:2d} ref {row['reference_passes']:2d} acc {row['accepts_expected']:2d} "
                  f"rej {row['rejects_wrong']:3d}/{row['wrong_total']:3d} und {row['undecidable']}  "
                  f"{(row['errors'] or [''])[0][:60]}", flush=True)
    return cmd_summary(ds, args, kind="validation")


def cmd_reference(ds, args):
    from FormalLLM.lean.evaluate import score_code
    from FormalLLM.lean.session import LeanSession
    path = ds.result_path("reference_scores.jsonl")
    if args.redo and os.path.exists(path):
        os.remove(path)
    done = {r["task"] for r in read_jsonl(path)}
    todo = [i for i in select(ds, args) if i not in done]
    print(f"reference {ds.name}: {len(todo)} to do, {len(done)} already in {path}", flush=True)
    with LeanSession(imports=args.imports, startup_timeout=1800) as lean, open(path, "a", encoding="utf8") as out:
        for i in todo:
            row = score_code(lean, ds.load(i))
            row["family"] = ds.family(i)
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
            out.flush()
            print(f"{i:44s} compiles={row['compiles']!s:5s} tests {row['passed']:2d}/{row['tests']:2d} "
                  f"unproved {row['unproved']} {row['seconds']:5.1f}s {(row['errors'] or [''])[0][:60]}", flush=True)
    return cmd_summary(ds, args, kind="reference")


def _append_jsonl(path, redo):
    if redo and os.path.exists(path):
        os.remove(path)
    return open(path, "a", encoding="utf8")


def cmd_compile(ds, args):
    from FormalLLM.lean.evaluate import task_source
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import PROOF, strip_imports
    path = ds.result_path("compile_check_noproof.jsonl" if args.no_proof else "compile_check.jsonl")
    rows = []
    with LeanSession(imports=args.imports, startup_timeout=1800) as lean, _append_jsonl(path, True) as out:
        for i in select(ds, args):
            task = ds.load(i)
            text = task_source(task)
            if args.no_proof:
                text = PROOF.sub(lambda m: m.group(1) + "  sorry" + m.group(2), text)
            reply, env = lean.load(task.compat + "\n" + strip_imports(text), timeout=240)
            sorry = bool(reply.goals) or any("sorry" in w for w in reply.warnings)
            status = "ERROR" if env is None else ("SORRY" if sorry else "CLEAN")
            row = {"task": i, "status": status, "errors": [e[:300] for e in reply.errors[:3]], "seconds": round(reply.seconds, 2)}
            rows.append(row)
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"{i:44s} {status:6s} {reply.seconds:6.1f}s {(row['errors'] or [''])[0][:70]}", flush=True)
    count = {k: sum(r["status"] == k for r in rows) for k in ("CLEAN", "SORRY", "ERROR")}
    print(f"{len(rows)} {ds.name} files: {count}")
    return 0


def cmd_goals(ds, args):
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import LeanSession
    rows = []
    with LeanSession(imports=args.imports, startup_timeout=1800) as lean, _append_jsonl(ds.result_path("goal_check.jsonl"), True) as out:
        for i in select(ds, args):
            row = {"task": i, "family": ds.family(i), "reads": False, "loads": False, "error": ""}
            try:
                task = ds.load(i)
                row["reads"] = True
                Derivation(task, lean)._environment()
                row["loads"] = True
            except Exception as error:
                row["error"] = str(error)[:200].replace("\n", " ")
            rows.append(row)
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"{i:44s} loads={row['loads']!s:5s} {row['error'][:80]}", flush=True)
    print(f"{ds.name}: the engine opens the goal of {sum(r['loads'] for r in rows)} of {len(rows)} tasks")
    return 0


CASCADE = ("  set_option maxHeartbeats 400000 in\n  first\n"
           "    | (unfold {f} {f}_postcond; simp_all; done)\n    | (unfold {f} {f}_postcond; grind)\n"
           "    | (unfold {f} {f}_postcond; omega)\n    | (unfold {f} {f}_postcond; simp_all; omega)\n"
           "    | (unfold {f} {f}_postcond; simp_all; grind)\n    | (unfold {f} {f}_postcond; aesop)\n    | decide")


def cmd_automation(ds, args):
    from FormalLLM.lean.evaluate import task_source
    from FormalLLM.lean.session import LeanSession
    from FormalLLM.lean.task import PROOF, strip_imports
    rows = []
    with LeanSession(imports=args.imports, startup_timeout=1800) as lean, _append_jsonl(ds.result_path("automation_scores.jsonl"), True) as out:
        for i in select(ds, args):
            task = ds.load(i)
            text = PROOF.sub(lambda m: m.group(1) + CASCADE.format(f=task.name) + m.group(2), task_source(task))
            reply, env = lean.load(task.compat + "\n" + strip_imports(text), timeout=300)
            status = "PROVED" if env is not None and not reply.goals else "NOT_PROVED"
            row = {"task": i, "status": status, "errors": [e[:200] for e in reply.errors[:2]], "seconds": round(reply.seconds, 1)}
            rows.append(row)
            out.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"{i:44s} {status:10s} {reply.seconds:6.1f}s", flush=True)
    print(f"{sum(r['status'] == 'PROVED' for r in rows)} of {len(rows)} {ds.name} postconditions proved by the cascade alone "
          "(reference code given, no model)")
    return 0


def cmd_oracles(ds, args):
    from benchmarks.datasets import lean_oracle
    from FormalLLM.lean.session import DEFAULT_IMPORTS, FULL_IMPORTS
    table = ds.oracles()
    if not table:
        print(f"no hand-written derivations for {ds.name}")
        return 2
    imports = "full" if args.imports.strip() == FULL_IMPORTS else "default"
    only = args.only
    if args.module:                       # only the derivations of one batch module (its ORACLES_MORE)
        import importlib
        only = list(importlib.import_module(f"benchmarks.datasets.{args.module}").ORACLES_MORE)
    rows = lean_oracle.run(only, imports, oracles=table, library=ds.root)
    with open(ds.result_path("oracle.json"), "w", encoding="utf8") as handle:
        json.dump(rows, handle, indent=1, ensure_ascii=False)
    print(f"\n{sum(r['certified'] for r in rows)} of {len(rows)} {ds.name} derivations certified "
          f"({sum(r['accepted'] for r in rows)} accepted by the engine); {len(table)} exist, "
          f"{len(ds.ids())} tasks in the dataset")
    return 0


def cmd_summary(ds, args, kind=None):
    from FormalLLM.lean.evaluate import solved, validation_ok
    kinds = [kind] if kind else ["validation", "reference"]
    for k in kinds:
        path = ds.result_path("validation.jsonl" if k == "validation" else "reference_scores.jsonl")
        rows = read_jsonl(path)
        if not rows:
            print(f"{ds.name}: no {k} results ({path})")
            continue
        if k == "validation":
            print(f"\n{ds.name} validation, {len(rows)} tasks:")
            print(f"  compile                         {sum(r['compiles'] for r in rows)}")
            print(f"  tests                           {sum(r['tests'] for r in rows)}")
            print(f"  reference passes                {sum(r['reference_passes'] for r in rows)}")
            print(f"  postcondition accepts expected  {sum(r['accepts_expected'] for r in rows)}")
            print(f"  postcondition rejects wrong     {sum(r['rejects_wrong'] for r in rows)} / {sum(r['wrong_total'] for r in rows)}")
            print(f"  tasks with all four checks ok   {sum(validation_ok(r) for r in rows)} / {len(rows)}")
            bad = [r["id"] for r in rows if not validation_ok(r)]
            if bad:
                print("  to look at:", ", ".join(bad[:25]) + (" ..." if len(bad) > 25 else ""))
        else:
            print(f"\n{ds.name} reference solutions, {len(rows)} tasks:")
            print(f"  compile                         {sum(r['compiles'] for r in rows)}")
            print(f"  compile and pass every test     {sum(solved(r) for r in rows)}")
            print(f"  compile, a test errors          {sum(r['compiles'] and r['unproved'] > 0 for r in rows)}")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", choices=["list", "validate", "reference", "compile", "goals", "automation", "oracles", "summary"])
    ap.add_argument("--dataset", default="humaneval")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--imports", default="import Mathlib")
    ap.add_argument("--redo", action="store_true")
    ap.add_argument("--module", default="", help="oracles: only the derivations of this batch module (benchmarks/datasets/<name>.py)")
    ap.add_argument("--no-proof", action="store_true", help="compile: replace each task's proof by sorry first")
    args = ap.parse_args()
    from FormalLLM.lean.dataset import get
    ds = get(args.dataset)
    commands = {"list": cmd_list, "validate": cmd_validate, "reference": cmd_reference, "compile": cmd_compile, "goals": cmd_goals,
                "automation": cmd_automation, "oracles": cmd_oracles, "summary": cmd_summary}
    return commands[args.command](ds, args)


if __name__ == "__main__":
    sys.exit(main())
