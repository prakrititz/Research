"""Free replay: feed a stored run's replies (refinement and proof calls, in call order) back through the CURRENT agent code.
No model is called; a scripted provider returns the stored answers. Usage: python replay_run.py <results.jsonl>"""
import json, os, sys
S = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(S, "rc2"))
os.chdir(os.path.join(S, "rc2"))
os.environ["FORMALLLM_FIXES"] = "2,3,4,5,6"
os.environ.pop("FORMALLLM_PROOF_CONFIG", None)          # proof calls also come from the stored list, in order
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
from FormalLLM.lean import dataset as d
from FormalLLM.lean.agent import LeanAgent
from FormalLLM.lean.session import LeanSession, FULL_IMPORTS
from FormalLLM.llm.provider import LLMProvider


class Stored(LLMProvider):
    def __init__(self, replies):
        self.replies, self.used = list(replies), 0

    def generate(self, prompt, max_tokens=None):
        self.used += 1
        return self.replies.pop(0) if self.replies else ""


rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf8") if l.strip()]
with LeanSession(imports=FULL_IMPORTS) as lean:
    for r in rows:
        task = d.resolve(r["task"]).load(r["task"])
        provider = Stored(r["replies"])
        result = LeanAgent(provider, max_calls=len(r["replies"])).solve(task, lean)
        print(f"{r['task']:24s} stored: {r['outcome']:9s} -> replayed with current code: {result.outcome:9s} "
              f"verified={result.verified}  (used {provider.used}/{len(r['replies'])} stored replies)  {result.detail[:100]}",
              flush=True)
