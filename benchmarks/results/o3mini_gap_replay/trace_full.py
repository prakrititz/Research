"""Replay a task normally, logging every helper-lemma attempt and every obligation verdict."""
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
    orig_h, orig_c, orig_run = der._prove_as_helper, der._check_once, der._run
    def helper(ob, name, tac):
        t0 = time.time(); ok = orig_h(ob, name, tac)
        print(f"HELPER {name} {ob.description[:50]!r} ok={ok} {time.time()-t0:.0f}s :: {tac[-70:]}", flush=True); return ok
    def check(ob, name):
        t0 = time.time(); v = orig_c(ob, name)
        print(f"CHECK {name} {ob.description[:50]!r} {v.status} {time.time()-t0:.0f}s {v.message[:120]!r}", flush=True); return v
    def run(src, timeout=None):
        r = orig_run(src, timeout)
        if r.timed_out: print(f"  RUN timed out after {timeout or der.timeout}s", flush=True)
        if "refine_portfolio" in src:
            print("  PORTFOLIO errors:", [e[:300] for e in r.errors[:2]], "infos:", [i[:80] for i in r.infos[:6]], flush=True)
        return r
    orig_admit = der._admit
    def admit(lemma):
        v = orig_admit(lemma)
        if v is not None:
            print("  ADMIT FAILED", lemma.name, v.status, v.message[:600], "PROOF:", lemma.proof[-400:], flush=True)
        return v
    der._prove_as_helper, der._check_once, der._run, der._admit = helper, check, run, admit
    steps = der.apply_tree(tree)
    print("STEPS", [(s.ok, s.status) for s in steps])
