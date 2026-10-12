r"""Re-verify the hand-written derivations in a fresh, plain Lean process (not the REPL the engine used).

    python benchmarks/verify_derivations.py --dataset lean_specs [--only ID ...] [--workers 2]
    python benchmarks/verify_derivations.py --dataset verina

For every derivation of the dataset the engine (one session) produces the finished Lean file. Each file is then written to disk and
compiled by ``lake env lean`` in its own process, and four things are checked from that process's output alone:

1. **no error** (the whole term, with the loops' termination proofs, type-checks);
2. **axioms**: ``#print axioms <f>_spec_satisfied`` lists nothing but ``propext``, ``Classical.choice``, ``Quot.sound``
   (no ``sorryAx``, no ``Lean.ofReduceBool`` from ``native_decide``, no declared axiom);
3. **the statement is the dataset's own**: the file's precondition, postcondition and their auxiliary definitions are the text of
   the dataset's ``task.lean`` regions (a derivation cannot have proved a weaker statement);
4. **the program runs and passes the task's tests** (each ``test.json`` case printed ``true`` by ``#eval``).

Output: ``benchmarks/results/<dataset>/verification.json`` and the compiled files under ``.../verified/``.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REGION = {name: re.compile(r"-- !benchmark @start %s\n(.*?)\n?\s*-- !benchmark @end %s" % (name, name), re.S)
          for name in ("precond_aux", "precond", "postcond_aux", "postcond")}


def squash(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def statement_is_datasets_own(task, source: str) -> list:
    """The regions of the dataset's ``task.lean`` that must appear, as written, in the derivation's file."""
    original = open(os.path.join(task.directory, "task.lean"), encoding="utf8").read()
    flat, missing = squash(source), []
    for name, pattern in REGION.items():
        match = pattern.search(original)
        text = squash(match.group(1)) if match else ""
        # the engine renders ``precond`` etc. with the same text; a region may be empty (no helpers)
        if text and text not in flat:
            missing.append(name)
    return missing


def produce(ds, ids, trees, out_dir):
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.session import LeanSession
    produced = {}
    with LeanSession(imports="import Mathlib", startup_timeout=1800) as lean:
        for task_id in ids:
            task = ds.load(task_id)
            entry = {"id": task_id, "laws": 0, "helpers": 0, "complete": False}
            produced[task_id] = entry
            try:
                derivation = Derivation(task, lean)
                derivation.apply_tree(trees[task_id])
                entry.update(laws=derivation.laws_used, helpers=len(derivation.helpers), complete=derivation.complete)
                if not derivation.complete:
                    entry["error"] = "derivation incomplete"
                    continue
                source = derivation.source()
                entry["statement_regions_missing"] = statement_is_datasets_own(task, source)
                tests = "\n".join(task.test_commands())
                entry["tests_expected"] = len(task.test_commands())
                text = f"import Mathlib\n{task.compat}\n{source}\n{tests}\n"
                path = os.path.join(out_dir, f"{task_id}.lean")
                with open(path, "w", encoding="utf8", newline="\n") as handle:
                    handle.write(text)
                entry["file"] = path
            except Exception as error:                  # e.g. a task the session's imports cannot load
                entry["error"] = str(error)[:300]
            print(f"{task_id:36s} {'file written' if entry.get('file') else 'NO FILE: ' + entry.get('error', '')[:60]}", flush=True)
    return produced


def compile_file(entry, timeout):
    from FormalLLM.lean.session import Toolchain, short_path
    tool = Toolchain()
    started = time.time()
    try:
        done = subprocess.run(tool.command("lean", short_path(entry["file"])), cwd=short_path(tool.project), env=tool.env(),
                              capture_output=True, text=True, encoding="utf8", timeout=timeout)
        out = (done.stdout or "") + (done.stderr or "")
        code = done.returncode
    except subprocess.TimeoutExpired:
        out, code = "timeout", -1
    errors = [l for l in out.splitlines() if re.search(r":\d+:\d+: error", l)]
    axioms = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    listed = {a.strip() for a in axioms.group(1).split(",")} if axioms else (set() if "does not depend on any axioms" in out else None)
    trues = len(re.findall(r"(?m)^true$", out))
    entry.update(exit_code=code, errors=errors[:3], axioms=sorted(listed) if listed is not None else None,
                 axioms_standard=listed is not None and listed <= STANDARD, sorry_warning="declaration uses 'sorry'" in out
                 or "declaration uses `sorry`" in out, tests_true=trues, seconds=round(time.time() - started, 1))
    entry["verified"] = bool(code == 0 and not errors and entry["axioms_standard"] and not entry["sorry_warning"]
                             and not entry.get("statement_regions_missing") and trues == entry.get("tests_expected", -1))
    return entry


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", default="lean_specs")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=900)
    args = ap.parse_args()
    from FormalLLM.lean.dataset import get
    ds = get(args.dataset)
    trees = ds.oracles()
    ids = [i for i in ds.ids() if i in trees and (not args.only or i in args.only)]
    out_dir = os.path.join(ds.results_dir, "verified")
    os.makedirs(out_dir, exist_ok=True)
    produced = produce(ds, ids, trees, out_dir)
    todo = [e for e in produced.values() if e.get("file")]
    print(f"\ncompiling {len(todo)} files in fresh Lean processes ({args.workers} at a time)", flush=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for entry in pool.map(lambda e: compile_file(e, args.timeout), todo):
            print(f"{entry['id']:36s} {'VERIFIED' if entry['verified'] else 'NOT VERIFIED':13s} axioms={entry['axioms']} "
                  f"tests {entry['tests_true']}/{entry.get('tests_expected')} {entry['seconds']:6.1f}s "
                  f"{(entry['errors'] or [''])[0][:80]}", flush=True)
    rows = list(produced.values())
    with open(os.path.join(ds.results_dir, f"verification_{args.dataset}.json"), "w", encoding="utf8") as handle:
        json.dump(rows, handle, indent=1, ensure_ascii=False)
    print(f"\n{sum(bool(r.get('verified')) for r in rows)} of {len(rows)} derivations verified independently")


if __name__ == "__main__":
    main()
