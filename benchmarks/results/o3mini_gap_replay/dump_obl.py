"""For each task: replay its exported derivation (helper lemmas removed, hammer stage off) and write a Lean file with the
task environment and every obligation that failed, each proved by `refine_portfolio_debug` (which reports open goals)."""
import json, os, sys
root = sys.argv[1]
sys.path.insert(0, root); sys.path.insert(0, os.path.join(root, "benchmarks"))
from prover_ceiling import strip_lemmas
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
outdir, task_ids = sys.argv[2], sys.argv[3:]
E.HAMMER = os.environ.get("DUMP_HAMMER") == "1"     # on: get past obligations the portfolio proves
with LeanSession(imports=FULL_IMPORTS) as lean:
    for task_id in task_ids:
        lean.recycle()
        folder = "classic" if task_id.startswith("classic") else "humaneval"
        tree, _ = strip_lemmas(json.load(open(os.path.join(root, "exports", folder, task_id, "derivation.json"), encoding="utf8")))
        task = datasets.resolve(task_id).load(task_id)
        der = E.Derivation(task, lean, counterexamples=False)
        steps = der.apply_tree(tree)
        prep = (f"(try unfold {task.post_name} {task.pre_name} at *); (try dsimp only at *); (try intros); "
                "(try casesm* _ ∧ _); (repeat' apply And.intro) <;> (try intros) <;> refine_portfolio_debug")
        out = os.path.join(outdir, task_id + ".lean")
        with open(out, "w", encoding="utf8") as f:
            f.write("import LeanEnv.Hammer\n" + der.lemmas + "\n" + task.prelude + "\n" + der._helper_text() + "\n")
            k = 0
            for s in steps:
                for v in s.verdicts:
                    if v.status != "PROVED":
                        f.write(f"-- {v.status}: {v.obligation.description}\n-- {v.message[:200]}\n")
                        f.write(v.obligation.source(f"obl{k}", prep) + "\n")
                        k += 1
        print("written", out, k, "failing obligations", flush=True)
