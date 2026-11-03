"""Replay a logged trial's applied steps up to reply K, apply reply K (lemmas dropped, strict), and dump every Lean source
the engine sends and its errors.
    python repro_step.py <rc2 root> <trials.jsonl> <task> <k> <outdir>"""
import json, os, sys
root, trials, task_id, k, outdir = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
sys.path.insert(0, root)
from FormalLLM.lean import dataset as datasets
import FormalLLM.lean.engine as E
from FormalLLM.lean.laws import law_from_json
from FormalLLM.lean.session import FULL_IMPORTS, LeanSession

trial = next(json.loads(l) for l in open(os.path.join(root, trials), encoding="utf8") if json.loads(l)["task"] == task_id)
sent = []
with LeanSession(imports=FULL_IMPORTS) as lean:
    task = datasets.resolve(task_id).load(task_id)
    der = E.Derivation(task, lean, counterexamples=True)
    run = der._run
    def logged(source, timeout=None):
        reply = run(source, timeout)
        sent.append((source, reply))
        return reply
    der._run = logged
    # the logged trajectory: the goal each reply targeted is the agent's choice; re-apply the replies applied before K
    goals = [None] * len(trial["replies"])
    rows = trial.get("calls") or []
    retracted = [int(x) for x in sys.argv[8].split(",")] if len(sys.argv) > 8 else []
    for j in range(k):
        if trial["call_outcomes"][j] != "applied" and j not in retracted:
            continue
        data = json.loads(trial["replies"][j])
        data.pop("lemmas", None)
        goal = int(sys.argv[6].split(",")[j]) if len(sys.argv) > 6 else der.open_goals()[0].id
        step = der.apply(goal, law_from_json(data))
        print("applied", j, "at goal", goal, step.ok, flush=True)
        if j in retracted and step.ok:
            der.retract(goal)                       # gate B: applied now, refused in the logged run
            print("  retracted; helpers now", [h.name for h in der.helpers], flush=True)
    data = json.loads(trial["replies"][k])
    data.pop("lemmas", None)
    goal = int(sys.argv[7]) if len(sys.argv) > 7 else der.open_goals()[0].id
    sent.clear()
    step = der.apply(goal, law_from_json(data))
    print("reply", k, "at goal", goal, "ok", step.ok, step.message[:300])
    for v in step.verdicts:
        print("  ", v.status, v.obligation.kind, v.message[:200].replace("\n", " | "))
    with open(os.path.join(outdir, f"{task_id}_{k}.txt"), "w", encoding="utf8") as f:
        for source, reply in sent:
            f.write("=" * 100 + "\n" + source + "\n--- errors:\n" + "\n".join(reply.errors)[:3000] + "\n")
    print("sources:", len(sent))
