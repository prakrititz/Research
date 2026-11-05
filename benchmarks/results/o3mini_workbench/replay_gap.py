"""Fix 1 offline test: replay stored o3-mini trials that hit 'no tactic of the cascade closes this' through the CURRENT
engine/agent in this tree (no model calls) and report outcome flips. Usage: python replay_gap.py <tree> <results.jsonl> <out.jsonl>"""
import json, os, sys, time
tree, src, out = sys.argv[1], sys.argv[2], sys.argv[3]
sys.path.insert(0, tree)
os.chdir(tree)
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
from FormalLLM.lean import dataset as datasets
from FormalLLM.lean.agent import LeanAgent
from FormalLLM.lean.session import LeanSession, FULL_IMPORTS
from FormalLLM.llm.provider import LLMProvider


class Stored(LLMProvider):
    def __init__(self, replies):
        self.replies = list(replies)

    def generate(self, prompt, max_tokens=None):
        return self.replies.pop(0) if self.replies else ""


rows = [json.loads(l) for l in open(src, encoding="utf8") if l.strip()]
rows = [r for r in rows if r["outcome"] == "EXHAUSTED" and any("no tactic of the cascade closes" in m for m in r["feedback"])]
done = set()
if os.path.exists(out):
    done = {json.loads(l)["task"] for l in open(out, encoding="utf8") if l.strip()}
print(f"{len(rows)} prover-gap trials, {len(done)} already replayed", flush=True)
with LeanSession(imports=FULL_IMPORTS) as lean, open(out, "a", encoding="utf8") as handle:
    for r in rows:
        if r["task"] in done:
            continue
        t0 = time.time()
        try:
            task = datasets.resolve(r["task"]).load(r["task"])
            res = LeanAgent(Stored(r["replies"]), max_calls=len(r["replies"])).solve(task, lean)
            new, ver = res.outcome, res.verified
        except Exception as e:
            new, ver = "ERROR:" + str(e)[:80], False
        rec = {"task": r["task"], "old": r["outcome"], "new": new, "verified": ver, "seconds": round(time.time() - t0, 1)}
        handle.write(json.dumps(rec) + "\n"); handle.flush()
        print(rec, flush=True)
