"""Gate B: re-judge every step a real model proposed (logged o3-mini trials) with today's prover, for free.

    python gate_b.py <rc2 root> <trials.jsonl> <out.jsonl> [--limit N] [--only TASK ...]

Each logged trial is replayed through the agent with its own replies, in order. The agent follows the ORIGINAL trajectory:
a reply is judged by the current engine (strict mode: the model's lemmas and proofs are dropped, the prover alone must prove
the step), but the agent is told the outcome the reply had in the logged run, so that later replies meet the goals they were
written for. A reply accepted now but refused then is withdrawn again after it is recorded. One row per reply:
    original / now (applied | unproved | ill_formed | timeout | ...), counterexample (a false step), open obligations.
A step that is `unproved` now without a counterexample is a candidate gap of the prover (true step, not proved).
"""
import argparse, json, os, sys, time

ap = argparse.ArgumentParser()
ap.add_argument("root"); ap.add_argument("trials"); ap.add_argument("out")
ap.add_argument("--limit", type=int, default=0)
ap.add_argument("--only", nargs="*")
args = ap.parse_args()
os.environ["FORMALLLM_FIXES"] = ""                      # no proof sub-agent: it would consume the scripted replies
os.environ["FORMALLLM_STRICT"] = "1"
sys.path.insert(0, args.root)
from FormalLLM.lean import dataset as datasets
from FormalLLM.lean import agent as A
from FormalLLM.lean import engine as E
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
from FormalLLM.llm.provider import LLMProvider


class Diverged(Exception):
    pass


class Scripted(LLMProvider):
    def __init__(self, replies):
        self.replies = list(replies)

    def generate(self, prompt, max_tokens=None):
        return self.replies.pop(0) if self.replies else ""


rows_out = []
_apply = A.LeanAgent._apply
def apply(self, derivation, goal, prompt, reply, failures):
    k = self._k
    self._k += 1
    original = self._original[k] if k < len(self._original) else "?"
    started = time.time()
    call = _apply(self, derivation, goal, prompt, reply, failures)
    row = {"task": self._task, "k": k, "goal": goal.id, "original": original, "now": call.outcome,
           "seconds": round(time.time() - started, 1), "reply": reply[:600]}
    data, steps = getattr(self, "_last", (None, None))
    if call.outcome != "applied" and steps:
        bad = [v for v in steps[-1].verdicts if not v.proved]
        row["counterexample"] = any(v.counterexample for v in bad)
        row["open"] = [v.obligation.description for v in bad]
        row["unsolved"] = [g[:800] for v in bad for g in v.unsolved][:3]
        row["message"] = (bad[0].message if bad else steps[-1].message)[:400]
    else:
        row["message"] = call.feedback[:400]
    rows_out.append(row)
    if call.outcome == "applied" and original != "applied":
        derivation.retract(goal.id)                     # keep to the logged trajectory
    elif original == "applied" and call.outcome != "applied":
        raise Diverged(f"reply {k} was applied in the logged run, {call.outcome} now")
    return A.Call(goal.id, prompt, reply, original, call.feedback)
A.LeanAgent._apply = apply

trials = [json.loads(l) for l in open(args.trials, encoding="utf8") if l.strip()]
done = set()
if os.path.exists(args.out):
    done = {json.loads(l)["task"] for l in open(args.out, encoding="utf8") if l.strip()}
jobs = [t for t in trials if t["task"] not in done and t.get("replies") and (not args.only or t["task"] in args.only)]
if args.limit:
    jobs = jobs[:args.limit]
print(f"{len(jobs)} trials to replay ({len(done)} done)", flush=True)
with LeanSession(imports=FULL_IMPORTS) as lean, open(args.out, "a", encoding="utf8") as handle:
    for trial in jobs:
        lean.recycle()
        rows_out.clear()
        started = time.time()
        note = ""
        agent = A.LeanAgent(Scripted(trial["replies"]), max_calls=len(trial["replies"]))
        agent._k, agent._original, agent._task = 0, trial["call_outcomes"], trial["task"]
        try:
            task = datasets.resolve(trial["task"]).load(trial["task"])
            agent.solve(task, lean)
        except Diverged as error:
            note = f"diverged: {error}"
        except Exception as error:
            note = f"crash: {type(error).__name__}: {str(error)[:200]}"
        summary = {"task": trial["task"], "original_outcome": trial["outcome"], "replies": len(trial["replies"]),
                   "judged": len(rows_out), "note": note, "seconds": round(time.time() - started, 1), "steps": list(rows_out)}
        handle.write(json.dumps(summary, ensure_ascii=False) + "\n")
        handle.flush()
        gaps = sum(r["now"] == "unproved" and not r.get("counterexample") for r in rows_out)
        print(f"{trial['task']:36s} judged {len(rows_out)}/{len(trial['replies'])} "
              f"applied {sum(r['now'] == 'applied' for r in rows_out)} gaps {gaps} {summary['seconds']:6.1f}s {note[:60]}",
              flush=True)
