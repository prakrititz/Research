r"""Work on the obligations the prover leaves open, in the engine's own environment.

    python benchmarks/lean_probe.py FILE.lean [--task verina_advanced_47]   # one-shot: library (+ task definitions)
    python benchmarks/lean_probe.py dump he_020_find_closest_elements ...    # strict gold run; failing obligations to files
    python benchmarks/lean_probe.py serve DIR                                # run DIR/<task>__*.lean as they appear

``dump`` runs ``--model gold`` strictly (no helper lemmas) on the tasks and writes each obligation the prover refuses
to ``benchmarks/results/lspec/probe/<task>__<name>.lean`` as a theorem whose proof is ``sorry`` (replace it to try a
tactic), plus the cascade's unsolved goals in a comment.

``serve`` keeps one REPL with the lemma library and each task's definitions loaded, and runs every new
``DIR/<task>__*.lean`` (or ``DIR/lib__*.lean`` for the library alone) once, writing the errors, infos and goals to the
``.out`` file next to it. Rewriting a ``.lean`` file runs it again. Stop it with ``DIR/STOP``. Each file gets
``PROBE_TIMEOUT`` seconds (default 180)."""
import argparse
import glob
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))
PROBE = os.path.join(ROOT, "benchmarks", "results", "lspec", "probe")


def dump(task_ids):
    import json
    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.engine import Derivation
    from FormalLLM.lean.lspec_agent import GoldModel, LSpecAgent
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))
    os.makedirs(PROBE, exist_ok=True)
    original = Derivation._check

    def recording(self, obligation, name):
        verdict = original(self, obligation, name)
        if not verdict.proved and obligation.body is None:
            goals = "\n\n".join(verdict.unsolved)[:6000]
            path = os.path.join(PROBE, f"{self.task.id}__{name}.lean")
            with open(path, "w", encoding="utf8") as handle:
                handle.write(f"/- {obligation.kind}: {obligation.description}\n{verdict.status}: {verdict.message}\n"
                             f"{verdict.counterexample or ''}\nunsolved:\n{goals}\n-/\n"
                             f"theorem probe {obligation.binders} :\n    {obligation.statement} := by\n  sorry\n")
            print("  wrote", os.path.relpath(path, ROOT), flush=True)
        return verdict
    Derivation._check = recording
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        for task_id in task_ids:
            dataset = next(k for k, v in trees.items() if task_id in v)
            task = resolve(task_id).load(task_id)
            agent = LSpecAgent(GoldModel(trees[dataset][task_id]), "joint", 30, 1, 0, 3, True)
            result = agent.solve(task, lean)
            print(f"{task_id}: {result.outcome} {result.detail}", flush=True)


def serve(folder):
    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.engine import AUTO_CLOSE
    from FormalLLM.lean.lemmas import LEMMAS
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    os.makedirs(folder, exist_ok=True)
    seen, envs = {}, {}
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        print("ready", flush=True)
        while not os.path.exists(os.path.join(folder, "STOP")):
            for path in sorted(glob.glob(os.path.join(folder, "*__*.lean"))):
                try:
                    stamp = os.path.getmtime(path)
                    text = open(path, encoding="utf8").read()
                except OSError:                       # removed since the listing
                    continue
                out = path[:-5] + ".out"
                if path not in seen and os.path.exists(out) and os.path.getmtime(out) >= stamp:
                    seen[path] = stamp                # answered by an earlier server
                    continue
                if seen.get(path) == stamp:
                    continue
                seen[path] = stamp
                task_id = os.path.basename(path).split("__")[0]
                started = time.time()
                try:
                    library = lean.library_env(LEMMAS + "\n" + AUTO_CLOSE)
                    if task_id != "lib" and (task_id, lean.restarts) not in envs:
                        task = resolve(task_id).load(task_id)
                        reply, env = lean.load(task.compat + "\n" + task.prelude, timeout=600, env=library)
                        if env is None:
                            raise ValueError("; ".join(reply.errors[:2]))
                        envs[(task_id, lean.restarts)] = env
                    env = library if task_id == "lib" else envs[(task_id, lean.restarts)]
                    reply = lean.run(text, env=env, timeout=float(os.environ.get("PROBE_TIMEOUT", "180")))
                    lines = [f"{'OK' if reply.ok and not reply.goals else 'FAIL'} {time.time() - started:.1f}s"
                             + (" TIMEOUT" if reply.timed_out else "")]
                    lines += ["ERROR: " + e[:3000] for e in reply.errors[:6]]
                    lines += ["INFO: " + i[:3000] for i in reply.infos[:20]]
                    lines += ["GOAL:\n" + g[:3000] for g in reply.goals[:4]]
                except Exception as error:
                    lines = [f"PROBE ERROR {type(error).__name__}: {error}"]
                with open(path[:-5] + ".out", "w", encoding="utf8") as handle:
                    handle.write("\n".join(lines) + "\n")
                print(os.path.basename(path), lines[0], flush=True)
            time.sleep(1)


def run(files, task_id):
    """One-shot: each file in the library environment (plus the task's definitions), errors / infos / goals printed."""
    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.lemmas import LEMMAS
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    prelude = ""
    if task_id:
        task = resolve(task_id).load(task_id)
        prelude = task.compat + "\n" + task.prelude
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        reply, env = lean.load(LEMMAS + "\n" + prelude, timeout=300)
        if env is None:
            raise SystemExit("the library/prelude does not load: " + "; ".join(e[:300] for e in reply.errors[:2]))
        for path in files:
            answer = lean.run(open(path, encoding="utf8").read(), env=env, timeout=300)
            print(f"== {os.path.basename(path)}: {'OK' if answer.ok else 'ERRORS'}")
            for error in answer.errors[:4]:
                print(error[:1800])
            for info in answer.infos:
                print(info[:1500])
            for goal in answer.goals[:3]:
                print("GOAL:\n" + goal[:1800])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", help="dump | serve | a .lean file (one-shot run, the original use)")
    ap.add_argument("args", nargs="*")
    ap.add_argument("--task", default="", help="one-shot run: also load this task's definitions")
    args = ap.parse_args()
    if args.mode == "dump":
        dump(args.args)
    elif args.mode == "serve":
        serve(args.args[0])
    else:
        run([args.mode, *args.args], args.task)


if __name__ == "__main__":
    main()
