"""Free re-check of the two failed measurement tasks: the model's stored values and proofs through the NEW proof checker
(unfold retry) and Lean's library search. No model calls."""
import json, os, sys
S = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(S, "rc2"))
os.chdir(os.path.join(S, "rc2"))
os.environ["FORMALLLM_FIXES"] = "2,3,4,5,6"
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
from FormalLLM.lean import dataset as d
from FormalLLM.lean.agent import LeanAgent, extract_json
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.laws import Term
from FormalLLM.lean.session import LeanSession, FULL_IMPORTS

rows = {r["task"]: r for r in (json.loads(l) for l in open("benchmarks/results/lean_agent/measure20.jsonl", encoding="utf8"))}
agent = LeanAgent(None)
with LeanSession(imports=FULL_IMPORTS) as lean:
    for task_id in ("he_034_unique", "he_069_search"):
        task = d.resolve(task_id).load(task_id)
        pairs, seen = [], set()
        replies = [extract_json(x) or {} for x in rows[task_id]["replies"]]
        value = None
        for data in replies:                      # (value, proof) pairs, in order; proof-only replies belong to the last value
            if data.get("law") == "term":
                value = data["expr"]
            if value and data.get("proof"):
                pairs.append((value, data["proof"]))
        values = list(dict.fromkeys(v for v, _ in pairs))
        print(f"\n== {task_id}: {len(values)} distinct values, {len(pairs)} proofs sent by the model")
        for value in values:
            der = Derivation(task, lean, counterexamples=False)
            step = der.apply(der.root.goal.id, Term(value))
            if step.ok:
                print(f"  value accepted by the automation outright: {value[:70]}"); continue
            bad = [v for v in step.verdicts if not v.proved]
            if len(bad) != 1 or bad[0].status != "UNPROVED":
                print(f"  value {value[:60]!r}: {[(v.status, v.message[:80]) for v in bad]}"); continue
            lemma, hint = agent._library_search(der, "srch", bad[0].obligation)
            print(f"  value {value[:60]!r}: library search {'PROVES IT' if lemma else 'does not close it'}"
                  + (f"; hints: {hint[:200]!r}" if hint else ""))
            ok = 0
            for k, (v, proof) in enumerate(p for p in pairs if p[0] == value):
                lem, msg = agent._check_proof(der, f"chk{k}", bad[0].obligation, proof)
                ok += lem is not None
                if lem is None:
                    print(f"     proof {k}: still fails: {msg[:160]!r}")
            print(f"     model's own proofs now accepted: {ok}")
