import json, os, sys, time
sys.path.insert(0, sys.argv[1])
sys.path.insert(0, os.path.join(sys.argv[1], "benchmarks"))
from prover_ceiling import strip_lemmas
from FormalLLM.lean import dataset as datasets
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
task_id = sys.argv[2]
tree, _ = strip_lemmas(json.load(open(os.path.join(sys.argv[1], "exports", "humaneval", task_id, "derivation.json"), encoding="utf8")))
with LeanSession(imports=FULL_IMPORTS) as lean:
    task = datasets.resolve(task_id).load(task_id)
    der = Derivation(task, lean, counterexamples=False)
    steps = der.apply_tree(tree)
    print("ok steps", all(s.ok for s in steps), der.complete)
    c = der.certify()
    print("compiles", c.compiles, "axioms", repr(c.axioms), "tests", c.tests, "passed", c.passed, "errors", c.errors)
    src = der.source()
    open(sys.argv[3], "w", encoding="utf8").write(src)
    tests = task.test_commands()
    prefix = task.compat + "\n" if task.compat else ""
    ran = lean.run(prefix + src + "\n" + "\n".join(tests), timeout=240)
    print("test errors", [e[:300] for e in ran.errors[:3]])
    print("infos", [i[:200] for i in ran.infos[-8:]])
