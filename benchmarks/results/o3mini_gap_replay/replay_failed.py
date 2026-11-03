"""Replay the recorded model replies of failed trials through the current code (no model call): which outcomes change, and
what feedback the model would now get."""
import json, os, sys
ROOT = sys.argv[1]
sys.path.insert(0, ROOT)
from FormalLLM.lean import dataset as datasets
from FormalLLM.lean.agent import LeanAgent
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
from FormalLLM.llm.provider import LLMProvider

class Stored(LLMProvider):
    def __init__(self, replies):
        self.replies = list(replies)
    def generate(self, prompt, max_tokens=None):
        return self.replies.pop(0) if self.replies else ""

rows = [json.loads(l) for f in sys.argv[2:] for l in open(f, encoding="utf8")]
rows = [r for r in rows if r["outcome"] != "SOLVED"]
with LeanSession(imports=FULL_IMPORTS) as lean:
    for row in rows:
        lean.recycle()
        task = datasets.resolve(row["task"]).load(row["task"])
        replies = [r for r in row["replies"] if r]
        result = LeanAgent(Stored(replies), max_calls=len(replies)).solve(task, lean)
        print(f"\n##### {row['task']}: stored {row['outcome']} -> replayed {result.outcome}/{result.verified}", flush=True)
        print("  stored  :", row["call_outcomes"])
        print("  replayed:", [c.outcome for c in result.calls])
        for c in result.calls:
            if c.outcome != "applied":
                print("  --", c.outcome, "|", c.feedback.replace("\n", " ")[:400])
