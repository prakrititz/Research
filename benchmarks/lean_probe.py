r"""Run a scratch Lean file in the engine's environment: the lemma library, optionally a task's prelude.

    python benchmarks/lean_probe.py FILE.lean                      # lemma library only (namespace Refine)
    python benchmarks/lean_probe.py FILE.lean --task verina_advanced_47   # + the task's definitions (precond, postcond, helpers)

Prints the errors, the ``#check``/``#print`` output, and the goals of any ``sorry``/unsolved ``example``. Used while writing
helper lemmas: prove it here first, then paste it into a ``with_lemmas`` list.
"""
import argparse
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--task", default="")
    args = ap.parse_args()
    from FormalLLM.lean.dataset import resolve
    from FormalLLM.lean.lemmas import LEMMAS
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    prelude = ""
    if args.task:
        task = resolve(args.task).load(args.task)
        prelude = task.compat + "\n" + task.prelude
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        reply, env = lean.load(LEMMAS + "\n" + prelude, timeout=300)
        if env is None:
            raise SystemExit("the library/prelude does not load: " + "; ".join(e[:300] for e in reply.errors[:2]))
        for path in args.files:
            answer = lean.run(open(path, encoding="utf8").read(), env=env, timeout=300)
            print(f"== {os.path.basename(path)}: {'OK' if answer.ok else 'ERRORS'}")
            for error in answer.errors[:4]:
                print(error[:1800])
            for info in answer.infos:
                print(info[:1500])
            for goal in answer.goals[:3]:
                print("GOAL:\n" + goal[:1800])


if __name__ == "__main__":
    main()
