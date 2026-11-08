"""A model writes every step of every derivation in L_spec; the translator turns it into Lean; Lean checks it.

    python benchmarks/lspec_applier.py --dataset humaneval --model gold --level prove --only he_003_below_zero
    python benchmarks/lspec_applier.py --dataset humaneval --model ollama:qwen3.5-nothink --level elaborate

Each step of the hand-written derivations is a test case: the goal it starts from (shown in L_spec) and, as a perfect
selector, the law the derivation used there. The model writes the step; it is translated (``steps.to_engine``), the
law is applied to the goal, and the step is checked to ``--level``:

``translate``   the reply is a step, its L_spec parses, the law can be applied (no Lean)
``elaborate``   and every obligation it creates type-checks in Lean (the translation means something)
``prove``       and the prover proves every obligation (the step is accepted, as in a real run)

A refused attempt goes back to the model with the reason (``feedback.py``), up to ``--attempts`` times. Steps are tested
one at a time, each from its own goal, so one wrong step does not hide the others.

``--workflow``: ``applier`` (the law is given: the applier alone), ``split`` (a selector call chooses the law, then
the applier writes it), ``joint`` (one call chooses and writes). ``--model gold`` answers with the derivation's own
step (free: checks the harness and the translation). A paid model needs ``--max-usd`` and ``--paid-ok``.

Results: ``benchmarks/results/lspec/applier_<dataset>_<model>_<workflow>_<level>.jsonl``, one row per step (resumable
by task)."""
import argparse
import contextlib
import io
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.dsl import examples, feedback, prompts, steps  # noqa: E402

LEVELS = ("translate", "elaborate", "prove")


# --- the model --------------------------------------------------------------------------------------------------------

class Gold:
    """Answers with the derivation's own step (in L_spec)."""
    name = "gold"

    def __init__(self):
        self.current = None                                # the gold step of the goal being asked about
        self.scope = []                                    # that goal's variables

    def generate(self, prompt: str, max_tokens=None) -> str:
        if "Choose the law for this goal" in prompt:
            return json.dumps({"law": self.current["law"], "plan": ""})
        return json.dumps(steps.from_engine(self.current, self.scope), ensure_ascii=False)


class Replay:
    """Answers with the replies a model gave in an earlier run (``--model replay:<results.jsonl>``), in order, so a
    change to the translator or the checks is measured on the same answers without calling the model. A step whose
    earlier replies run out gets an empty answer."""

    def __init__(self, path: str):
        self.name = "replay"
        self.replies = {}
        for line in open(path, encoding="utf8"):
            row = json.loads(line)
            if row.get("path") is not None:
                self.replies[(row["id"], row["path"])] = [t["reply"] for t in row["tries"] if "reply" in t]
        self.queue = []

    def at(self, task_id: str, path: str):
        self.queue = list(self.replies.get((task_id, path), []))

    def generate(self, prompt: str, max_tokens=None) -> str:
        return self.queue.pop(0) if self.queue else ""


def make_model(spec: str, args):
    if spec == "gold":
        return Gold()
    if spec.startswith("replay:"):
        return Replay(spec.partition(":")[2])
    kind, _, config = spec.partition(":")
    from benchmarks import run_bench
    cfg = run_bench.CONFIGS[config]
    from FormalLLM.llm.provider import OpenAIChatProvider, is_self_hosted
    provider = run_bench.make_provider(cfg, args.temperature)
    # the server actually called decides: the remote gpt-oss behind ngrok (or localhost) is free; OpenAI, OpenRouter
    # and the like need a cap
    if cfg["kind"] != "ollama" and not is_self_hosted(provider.base_url):
        if args.max_usd is None or not args.paid_ok:
            raise SystemExit(f"{config} is a paid model ({provider.base_url}): pass --max-usd <cap> and --paid-ok "
                             "(after approval)")
        OpenAIChatProvider.MAX_BUDGET_USD = args.max_usd
    if cfg["kind"] == "ollama":
        provider.response_format = "json"
    provider.name = config
    return provider


def ask(model, prompt: str) -> str:
    with contextlib.redirect_stdout(io.StringIO()):         # providers print the prompt; keep the log readable
        return model.generate(prompt, max_tokens=4096)


# --- positioning a derivation at a step -------------------------------------------------------------------------------

def node_at(root, path: str):
    node = root
    for k in path.split(".")[1:]:
        node = node.children[int(k)]
    return node


class Positioned:
    """A real derivation of the task with the hand-written steps applied without proof (stubs), so any step's goal can
    be reopened (``open``) and a model's step checked there with the real prover, then the hand-written step put back
    (``restore``). The environment (lemma library, the task's definitions, the derivation's helper lemmas) is loaded
    once per task on top of the cached library (``lspec_equiv.base_env``)."""

    def __init__(self, task, tree: dict, lean):
        from FormalLLM.lean.engine import Derivation, Verdict
        from lspec_equiv import base_env
        self.d = d = Derivation(task, lean) if lean is not None else Derivation(task, None, counterexamples=False)
        self.tree, self.lean, self._verdict = tree, lean, Verdict
        if lean is not None:
            def environment():
                if d._env_id is None or d._env_restarts != lean.restarts:
                    reply, env = lean._run(task.prelude + "\n" + d._helper_text(), 600, base_env(lean, d.lemmas))
                    if env is None:
                        raise ValueError("the task's definitions do not load: " + (reply.errors or ["timeout"])[0][:300])
                    d._env_id, d._env_restarts = env, lean.restarts
                return d._env_id
            d._environment = environment
        self._stub()
        out = d.apply_tree(tree)
        if not all(s.ok for s in out) or not d.complete:
            raise ValueError("the hand-written derivation does not replay")
        self._unstub()

    def _stub(self):
        d, Verdict = self.d, self._verdict

        def admit(lemma):
            if not any(h.name == lemma.name for h in d.helpers):
                d.helpers.append(lemma)
            return None
        d._check = lambda obligation, name: Verdict(obligation, "PROVED")
        d._admit = admit

    def _unstub(self):
        for attr in ("_check", "_admit"):
            self.d.__dict__.pop(attr, None)

    def open(self, path: str):
        node = node_at(self.d.root, path)
        self.d.retract(node.goal.id)
        return node

    def restore(self, path: str, sub: dict):
        node = node_at(self.d.root, path)
        if node.law is not None:
            self.d.retract(node.goal.id)
        self._stub()
        try:
            self.d.apply_tree(sub, node.goal.id)
        finally:
            self._unstub()


# --- one step ---------------------------------------------------------------------------------------------------------

REPAIR = True                                              # --no-repair: Lean's verdict on the step as written
EXAMPLES, POOL = 0, "cross"                                # --examples / --pool: worked examples in the prompt


def check(pos: Positioned, node, written: dict, level: str):
    """Translate ``written`` and check it at ``node`` to ``level`` (``lspec_agent.judge``): (kind, message, note)."""
    from FormalLLM.lean.lspec_agent import judge
    loop_body = any(getattr(n.law, "kind", "") == "loop" and n.children and n.children[0] is node
                    for n in pos.d.nodes.values())
    verdict = judge(pos.d, node.goal, written, level, loop_body, REPAIR)
    return verdict.kind, verdict.message, verdict.note


def scope_of(goal) -> list:
    return [n for n, _ in goal.ctx] + [n for n, _ in goal.hyps]


def run_step(model, workflow: str, task, pos: Positioned, path: str, sub: dict, state, level: str, attempts: int):
    node = pos.open(path)
    shown = steps.goal_text(steps.goal_to_lspec(node.goal, state))
    gold = {k: v for k, v in sub.items() if k != "children"}
    if isinstance(model, Gold):
        model.current, model.scope = gold, scope_of(node.goal)
    tries, failures, law, plan = [], [], gold["law"], None
    started = time.time()
    try:
        for attempt in range(attempts):
            if workflow == "split" and (attempt == 0 or (tries and tries[-1]["to"] == "selector")):
                reply = ask(model, prompts.selector_prompt(task, shown, failures, examples.for_prompt(task, shown, None, EXAMPLES, POOL)))
                try:
                    chosen = prompts.parse_reply(reply)
                    law, plan = str(chosen.get("law")), chosen.get("plan")
                    steps.fields_for(law)
                except steps.StepError as error:
                    tries.append({"selector": reply[:300], "kind": feedback.UNREADABLE, "to": "selector",
                                  "feedback": feedback.unreadable(error)})
                    failures.append(f"Attempt {attempt + 1}: {tries[-1]['feedback']}")
                    continue
            if workflow == "joint":
                reply = ask(model, prompts.joint_prompt(task, shown, failures, examples.for_prompt(task, shown, None, EXAMPLES, POOL)))
            else:
                reply = ask(model, prompts.applier_prompt(task, shown, law, plan, failures,
                                                          examples.for_prompt(task, shown, law, EXAMPLES, POOL)))
            try:
                written = prompts.parse_reply(reply)
                if workflow != "joint":
                    written["law"] = law
                kind, message, note = check(pos, node, written, level)
            except steps.StepError as error:
                written, kind, message, note = None, feedback.UNREADABLE, feedback.unreadable(error), ""
            to = feedback.recipient(kind, attempt + 1) if workflow == "split" else "applier"
            tries.append({"law": (written or {}).get("law"), "reply": reply[:1500], "kind": kind,
                          "feedback": message[:1500], "to": to, **({"repaired": note} if note else {})})
            if kind == feedback.ACCEPTED:
                break
            failures.append(f"Attempt {attempt + 1}: {prompts.show_step(written) if written else reply[:300]}\n{message}")
    finally:
        pos.restore(path, sub)
    return {"law": gold["law"], "result": tries[-1]["kind"] if tries else "none", "attempts": len(tries),
            "chose_gold_law": [t.get("law") == gold["law"] for t in tries if "law" in t], "tries": tries,
            "goal": shown, "seconds": round(time.time() - started, 1)}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--limit", type=int, default=None, help="first N tasks")
    ap.add_argument("--model", default="gold", help="gold | ollama:<config> | <paid config>")
    ap.add_argument("--workflow", default="applier", choices=["applier", "split", "joint"])
    ap.add_argument("--level", default="elaborate", choices=LEVELS)
    ap.add_argument("--attempts", type=int, default=3)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--max-usd", type=float, default=None)
    ap.add_argument("--paid-ok", action="store_true")
    ap.add_argument("--no-repair", action="store_true", help="no conversions inserted (repair.py): Lean's verdict as written")
    ap.add_argument("--examples", type=int, default=0, help="worked examples from other tasks in each prompt")
    ap.add_argument("--pool", default="cross", choices=["cross", "others"])
    args = ap.parse_args()
    global REPAIR, EXAMPLES, POOL
    REPAIR, EXAMPLES, POOL = not args.no_repair, args.examples, args.pool
    from lspec_steps import walk
    from FormalLLM.lean.dataset import resolve
    model = make_model(args.model, args)
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    only = args.only
    if isinstance(model, Replay) and not only:
        only = sorted({task for task, _ in model.replies})
    ids = [t for t in trees if not only or t in only][:args.limit]
    tag = (f"replay-{os.path.splitext(os.path.basename(args.model[7:]))[0]}" if isinstance(model, Replay)
           else args.model.replace(":", "-")) + ("_norepair" if args.no_repair else "") + (
           f"_ex{args.examples}{args.pool}" if args.examples else "")
    out = os.path.join(ROOT, "benchmarks", "results", "lspec",
                       f"applier_{args.dataset}_{tag}_{args.workflow}_{args.level}.jsonl")
    done = set()
    if os.path.exists(out):
        done = {json.loads(line)["id"] for line in open(out, encoding="utf8") if line.strip()}

    def run(lean):
        for task_id in ids:
            if task_id in done:
                continue
            rows = []
            try:
                task = resolve(task_id).load(task_id)
                pos = Positioned(task, trees[task_id], lean)
                for path, node, sub, state in list(walk(pos.d.root, trees[task_id])):
                    if isinstance(model, Replay):
                        model.at(task_id, path)
                    row = run_step(model, args.workflow, task, pos, path, sub, state, args.level, args.attempts)
                    rows.append({"id": task_id, "path": path, **row})
            except Exception as error:
                rows.append({"id": task_id, "path": None, "result": "error", "error": f"{type(error).__name__}: {str(error)[:300]}"})
            with open(out, "a", encoding="utf8") as handle:
                for row in rows:
                    handle.write(json.dumps(row, ensure_ascii=False) + "\n")
            summary = " ".join(f"{r.get('law', '?')}:{r['result']}/{r.get('attempts', 0)}" for r in rows)
            print(f"{task_id:34s} {summary[:150]}", flush=True)
    if args.level == "translate":
        run(None)
    else:
        from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
        with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
            run(lean)
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    stepped = [r for r in rows if r.get("path") is not None]
    ok = sum(r["result"] == feedback.ACCEPTED for r in stepped)
    first = sum(r["result"] == feedback.ACCEPTED and r["attempts"] == 1 for r in stepped)
    print(f"{args.dataset} {args.model} {args.workflow} {args.level}: {ok}/{len(stepped)} steps accepted "
          f"({first} at the first attempt); {sum(r['result'] == 'error' for r in rows)} task errors")


if __name__ == "__main__":
    main()
