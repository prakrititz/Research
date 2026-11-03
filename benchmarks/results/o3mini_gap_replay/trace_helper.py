"""Replay a task with the hammer stage off; on the first failing obligation, run the portfolio helper path step by step."""
import json, os, sys, time
root = sys.argv[1]
sys.path.insert(0, root); sys.path.insert(0, os.path.join(root, "benchmarks"))
from prover_ceiling import strip_lemmas
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
task_id = sys.argv[2]
folder = "classic" if task_id.startswith("classic") else "humaneval"
tree, _ = strip_lemmas(json.load(open(os.path.join(root, "exports", folder, task_id, "derivation.json"), encoding="utf8")))
with LeanSession(imports=FULL_IMPORTS) as lean:
    task = datasets.resolve(task_id).load(task_id)
    der = E.Derivation(task, lean, counterexamples=False)
    E.HAMMER = False
    steps = der.apply_tree(tree)
    bad = [v for s in steps for v in s.verdicts if v.status != "PROVED"]
    ob = bad[0].obligation
    tac = der._hammer_tactics(ob)[0]
    orig = der._admit
    def admit(lemma):
        v = orig(lemma)
        print("ADMIT", lemma.name, "->", None if v is None else (v.status, v.message[:400]))
        print(lemma.source()[-700:])
        return v
    der._admit = admit
    print("RESULT", der._prove_as_helper(ob, "probe2", tac))
