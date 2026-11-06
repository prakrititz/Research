"""Every step of every hand-written derivation through the model's path: goal shown in L_spec, step written in L_spec,
step translated back to Lean, and Lean confirms nothing changed.

    python benchmarks/lspec_steps.py --dataset humaneval [--only ID ...] [--no-lean]

For each step (a node of the derivation, replayed with the prover stubbed out, as in ``lspec_equiv.py``):

1. the goal is rendered in L_spec (``steps.goal_to_lspec``) and read back: the statement it stands for must be the goal's
   own statement (``∀ inputs assumptions, ∃ result : T, property``);
2. the step is rendered in the model's format (``steps.from_engine``) and translated back (``steps.to_engine``): the law
   applied to the same goal must give the same obligations and the same sub-goals, and each helper lemma the same
   statement.

"Same" is ``#lspec_same``: structurally equal Lean terms (controls first). Pairs whose text is identical need no Lean.
With ``--no-lean`` only the translation is run (does every goal and step render and read back).

Results: ``benchmarks/results/lspec/steps_<dataset>.jsonl``, one row per step (resumable by task)."""
import argparse
import itertools
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.dsl import steps  # noqa: E402
from lspec_equiv import base_env, closed, collect, control  # noqa: E402


def _expansion(law, goal):
    """The obligations (closed statement, checked body) and sub-goal statements of ``law`` at ``goal``; fresh ids
    from a fixed start, so two laws give comparable names."""
    counter = itertools.count(100000)
    exp = law.expand(goal, lambda: next(counter))
    obligations = [(o.kind, closed(o.binders, o.statement),
                    o.body and (f"(fun {o.binders} => ({o.body} : {o.statement}))" if o.binders.strip()
                                else f"({o.body} : {o.statement})")) for o in exp.obligations]
    subgoals = [closed(g.binders(), f"∃ ρ : {g.ret}, {g.post.replace(steps.HOLE, 'ρ')}") for g in exp.subgoals]
    return obligations, subgoals


#: ``#lspec_same_beta`` must accept a lambda applied by hand and still tell different values apart
BETA_CONTROLS = [("((fun (x : Nat) => x + 1) 2)", "(2 + 1)", True), ("((fun (x : Nat) => x + 1) 2)", "(3 : Nat)", False),
                 ("((fun (x : Nat) (y : Nat) => x - y) 1 2)", "(2 - 1)", False)]


def control_beta(lean) -> None:
    from FormalLLM.lean.engine import AUTO_CLOSE
    from FormalLLM.lean.lemmas import LEMMAS
    env = base_env(lean, LEMMAS + "\n" + AUTO_CLOSE)
    for a, b, same in BETA_CONTROLS:
        reply = lean.run(f"#lspec_same_beta {a} {b}\n", timeout=120, env=env)
        if (not reply.errors and not reply.timed_out) != same:
            raise SystemExit(f"beta control failed: {a} vs {b} should be {'equal' if same else 'different'}: {reply.errors[:1]}")
    print(f"beta controls passed ({len(BETA_CONTROLS)})", flush=True)


def step_pairs(node, tree: dict, state=None):
    """(rendered goal, rendered step, [(what, original, after, check)]) for one step; ``state``: the state variables
    when the goal is a loop's body. ``check`` is the Lean command that compares the pair. Raises ``StepError``."""
    from FormalLLM.lean.laws import law_from_json
    goal = node.goal
    shown = steps.goal_to_lspec(goal, state)
    r = shown.get("as", shown["find"][0])
    binders, statement = steps.goal_from_lspec(shown)
    pairs = [("goal", closed(goal.binders(), f"∃ {r} : {goal.ret}, {goal.post.replace(steps.HOLE, r)}"),
              closed(binders, statement), "#lspec_same_beta" if "next" in shown else "#lspec_same")]
    gold = {k: v for k, v in tree.items() if k != "children"}
    scope = [n for n, _ in goal.ctx] + [n for n, _ in goal.hyps]
    written = steps.from_engine(gold, scope)
    back = steps.to_engine(written, scope)
    (ob1, sg1), (ob2, sg2) = _expansion(node.law, goal), _expansion(law_from_json(back), goal)
    if [k for k, *_ in ob1] != [k for k, *_ in ob2] or len(sg1) != len(sg2):
        raise steps.StepError("step", "the translated step gives a different number or kind of obligations")
    for (kind, s1, b1), (_, s2, b2) in zip(ob1, ob2):
        pairs.append((f"obligation {kind}", s1, s2, "#lspec_same"))
        if (b1 or "") != (b2 or ""):
            pairs.append((f"obligation {kind} (body)", b1 or "True", b2 or "True", "#lspec_same"))
    pairs += [("subgoal", a, b, "#lspec_same") for a, b in zip(sg1, sg2)]
    for l1, l2 in zip(gold.get("lemmas") or [], back.get("lemmas") or []):
        pairs.append((f"lemma {l1['name']}", f"({l1['statement']})", f"({l2['statement']})", "#lspec_same"))
    return steps.goal_text(shown), written, pairs


def walk(node, tree: dict, path: str = "0", state=None):
    """(path, node, tree step, loop state names or None) for every step, depth first, as ``apply_tree`` applied them;
    the state names are given for a loop's body."""
    yield path, node, tree, state
    inner = [n for n, _ in node.law.state] if getattr(node.law, "kind", "") == "loop" else None
    for k, (child, sub) in enumerate(zip(node.children, tree.get("children") or [])):
        yield from walk(child, sub, f"{path}.{k}", inner)


def check_task(task_id: str, tree: dict, lean):
    task, derivation, _ = collect(task_id, tree)
    rows = []
    env = None
    for path, node, sub, state in walk(derivation.root, tree):
        row = {"id": task_id, "path": path, "law": sub["law"], "ok": False, "pairs": 0, "checked": 0, "errors": []}
        try:
            row["goal"], row["step"], pairs = step_pairs(node, sub, state)
        except Exception as error:
            row["errors"].append(f"translation: {type(error).__name__}: {str(error)[:300]}")
            rows.append(row)
            continue
        row["pairs"] = len(pairs)
        different = [(what, a, b, how) for what, a, b, how in pairs if a != b]
        if different and lean is not None:
            if env is None:
                reply, env = lean._run(task.prelude + "\n" + derivation._helper_text(), 600,
                                       base_env(lean, derivation.lemmas))
                if env is None:
                    raise RuntimeError("environment: " + (reply.errors or ["timeout"])[0][:300])
            for what, a, b, how in different:
                reply = lean.run(f"{how} {a} {b}\n", timeout=300, env=env)
                row["checked"] += 1
                if reply.timed_out or reply.errors:
                    row["errors"].append({"what": what, "before": a[:400], "after": b[:400],
                                          "lean": (reply.errors or ["timeout"])[0][:500]})
        row["ok"] = not row["errors"] and (lean is not None or not different)
        row["unchecked"] = len(different) if lean is None else 0
        rows.append(row)
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--no-lean", action="store_true", help="translation only")
    args = ap.parse_args()
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    suffix = "_translation" if args.no_lean else ""
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"steps_{args.dataset}{suffix}.jsonl")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    done = set()
    if os.path.exists(out):
        done = {json.loads(line)["id"] for line in open(out, encoding="utf8") if line.strip()}
    todo = [t for t in trees if t not in done and (not args.only or t in args.only)]

    def run(lean):
        for task_id in todo:
            started = time.time()
            try:
                rows = check_task(task_id, trees[task_id], lean)
            except Exception as error:
                rows = [{"id": task_id, "path": None, "ok": False, "errors": [f"{type(error).__name__}: {str(error)[:300]}"]}]
            bad = [r for r in rows if not r["ok"]]
            print(f"{task_id:34s} steps {len(rows):2d}  {'OK ' if not bad else 'BAD'}  {round(time.time() - started, 1)}s  "
                  f"{'' if not bad else str(bad[0]['errors'][:1] or 'unchecked')[:180]}", flush=True)
            with open(out, "a", encoding="utf8") as handle:
                for row in rows:
                    handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    if args.no_lean:
        run(None)
    else:
        from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
        with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
            control(lean)
            control_beta(lean)
            run(lean)
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    tasks = {r["id"] for r in rows}
    bad_tasks = {r["id"] for r in rows if not r["ok"] and r.get("errors")}
    translated = sum(1 for r in rows if not any(isinstance(e, str) and e.startswith("translation") for e in r.get("errors", [])))
    print(f"{args.dataset}: {len(rows)} steps in {len(tasks)} tasks; {translated} steps translate both ways; "
          f"{sum(r['ok'] for r in rows)} steps " + ("identical in Lean" if not args.no_lean else "need no Lean check")
          + f"; {len(tasks) - len(bad_tasks)} of {len(tasks)} tasks without an error")


if __name__ == "__main__":
    main()
