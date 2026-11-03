"""Write the exact Lean file the engine checks for each obligation the cascade leaves open (helper lemmas removed,
hammer stage off): environment + `obligation.source(name, diagnose)`.
    python dump_exact.py <rc2 root> <outdir> TASK..."""
import json, os, sys
root = sys.argv[1]
sys.path.insert(0, root); sys.path.insert(0, os.path.join(root, "benchmarks"))
from prover_ceiling import strip_lemmas
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
outdir, task_ids = sys.argv[2], sys.argv[3:]
E.HAMMER = False
with LeanSession(imports=FULL_IMPORTS) as lean:
    for task_id in task_ids:
        lean.recycle()
        folder = "classic" if task_id.startswith("classic") else "humaneval"
        tree, _ = strip_lemmas(json.load(open(os.path.join(root, "exports", folder, task_id, "derivation.json"), encoding="utf8")))
        task = datasets.resolve(task_id).load(task_id)
        der = E.Derivation(task, lean, counterexamples=False)
        steps = der.apply_tree(tree)
        k = 0
        for s in steps:
            for v in s.verdicts:
                if v.status != "PROVED":
                    out = os.path.join(outdir, f"{task_id}_{k}.lean")
                    with open(out, "w", encoding="utf8") as f:
                        f.write("import LeanEnv.Hammer\n" + der.lemmas + "\n" + task.prelude + "\n" + der._helper_text() + "\n")
                        f.write(f"-- {v.status}: {v.obligation.description}\n-- {v.message[:300]}\n")
                        f.write(v.obligation.source(f"obl{k}", der.diagnose) + "\n")
                    print("written", out, v.status, v.message[:120], flush=True)
                    k += 1
