"""The specifications in L_spec: render every task's definitions (precondition, postcondition, helper functions) and
have Lean check that each rendered definition means exactly what the original does.

    python benchmarks/lspec_specs.py --dataset humaneval [--only ID ...] [--no-lean]

For each ``def`` the original source text and the L_spec round trip (Lean -> tree -> L_spec text -> tree -> Lean) are
both elaborated, as ``fun params => (body : ret)`` (a definition by cases: ``fun params => ((fun x.. => match x.. with
arms) : ret)``), in the task's own environment, and must give structurally equal terms (``#lspec_same`` of
``lspec_equiv.py``, with its controls). Commands the reader does not cover stay Lean and are counted.

Writes ``benchmarks/results/lspec/specs/<task>.lspec`` (what the model will read) and
``benchmarks/results/lspec/specs_<dataset>.jsonl`` (resumable)."""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.dsl import defs, lean_syntax, lspec_syntax  # noqa: E402


def roundtrip(node):
    return lspec_syntax.parse(lspec_syntax.show(node))


def term(params: str, ret: str, body: str = None, arms: str = None, n_pats: int = 0) -> str:
    """The definition as one term; each source piece on its own lines (a trailing `--` comment stays harmless)."""
    if arms is not None:
        xs = " ".join(f"x_{i}" for i in range(n_pats))
        # the arms keep their own indentation (Lean ends a match at an arm left of its first one)
        body = f"fun {xs} =>\nmatch {', '.join(f'x_{i}' for i in range(n_pats))} with\n{arms}\n"
    inner = f"(\n{body}\n : {ret}\n)" if ret else f"(\n{body}\n)"
    return f"(fun {params} =>\n{inner})" if params else inner


def pair(d: defs.Def):
    """(original term, L_spec round-trip term)."""
    n = len(d.arms[0][0]) if d.arms else 0
    before = term(d.src["params"], d.src.get("ret"), d.src.get("body"), d.src.get("arms"), n)
    params = [(v, roundtrip(t) if t is not None and v != "<pat>" else t) for v, t in d.params]
    ret = d.ret and lean_syntax.show(roundtrip(d.ret))
    if d.arms is not None:
        arms = "  " + lean_syntax.show_arms([([roundtrip(p) for p in pats], roundtrip(e)) for pats, e in d.arms], "\n  ")
        after = term(lean_syntax._binders(params), ret, arms=arms, n_pats=n)
    else:
        after = term(lean_syntax._binders(params), ret, lean_syntax.show(roundtrip(d.body)))
    return before, after


def same_consts(lean, env, before: str, after: str):
    """A term with `let rec` declares its functions, so the two sides cannot be elaborated side by side: each becomes a
    definition (``_lspec_a``, ``_lspec_b``) and ``#lspec_same_consts`` compares them and everything declared under
    them."""
    reply, env_a = lean._run(f"def _lspec_a :=\n{before}\n", 300, env)
    if env_a is None or reply.errors:
        return reply
    reply, env_b = lean._run(f"def _lspec_b :=\n{after}\n", 300, env_a)
    if env_b is None or reply.errors:
        return reply
    return lean.run("#lspec_same_consts _lspec_a _lspec_b\n", timeout=300, env=env_b)


#: ``same_consts`` must accept a reformatting and catch a change in the lifted helper or in the body
_GO = "(fun (n : Nat) => let rec go (n : Nat) (acc : Nat) : Nat := if n = 0 then acc else go (n / 10) (acc + {}); go n {})"
CONST_CONTROLS = [(_GO.format(1, 0), "(fun (n : Nat) =>\n  let rec go (n acc : Nat) : Nat :=\n"
                   "    if n = 0 then acc else go (n / 10) (acc + 1)\n  go n 0)", True),
                  (_GO.format(1, 0), _GO.format(2, 0), False),
                  (_GO.format(1, 0), _GO.format(1, 1), False)]


def control_consts(lean) -> None:
    from lspec_equiv import base_env
    from FormalLLM.lean.engine import AUTO_CLOSE
    from FormalLLM.lean.lemmas import LEMMAS
    env = base_env(lean, LEMMAS + "\n" + AUTO_CLOSE)
    for a, b, same in CONST_CONTROLS:
        reply = same_consts(lean, env, a, b)
        if (not reply.errors and not reply.timed_out) != same:
            raise SystemExit(f"let-rec control failed: {a} vs {b} should be {'equal' if same else 'different'}")
    print(f"let-rec controls passed ({len(CONST_CONTROLS)})", flush=True)


def check_task(task, lean) -> dict:
    from lspec_equiv import base_env
    from FormalLLM.lean.engine import AUTO_CLOSE
    from FormalLLM.lean.lemmas import LEMMAS
    items = defs.read(task.prelude)
    row = {"id": task.id, "defs": 0, "verbatim": [], "same": 0, "errors": []}
    rendered = []
    for item in items:
        if isinstance(item, defs.Verbatim):
            if not item.source.split()[0] in ("open", "set_option", "namespace", "end", "section"):
                row["verbatim"].append(item.why)
                rendered.append(defs.show_lspec(item))
            continue
        row["defs"] += 1
        rendered.append(defs.show_lspec(item))
    out_dir = os.path.join(ROOT, "benchmarks", "results", "lspec", "specs")
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, f"{task.id}.lspec"), "w", encoding="utf8") as handle:
        handle.write("\n\n".join(rendered) + "\n")
    if lean is None:
        return row
    reply, env = lean._run(task.prelude, 600, base_env(lean, LEMMAS + "\n" + AUTO_CLOSE))
    if env is None:
        row["errors"].append("environment: " + (reply.errors or ["timeout"])[0][:300])
        return row
    for item in items:
        if not isinstance(item, defs.Def):
            continue
        try:
            before, after = pair(item)
        except Exception as error:
            row["errors"].append({"def": item.name, "python": f"{type(error).__name__}: {str(error)[:200]}"})
            continue
        if "let rec" in before:
            reply = same_consts(lean, env, before, after)
        else:
            reply = lean.run(f"#lspec_same {before} {after}\n", timeout=300, env=env)
        if reply.timed_out or reply.errors:
            row["errors"].append({"def": item.name, "before": before[:500], "after": after[:500],
                                  "lean": (reply.errors or ["timeout"])[0][:600]})
        else:
            row["same"] += 1
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", required=True, choices=["humaneval", "classic", "verina"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--no-lean", action="store_true", help="render only")
    args = ap.parse_args()
    from FormalLLM.lean.dataset import resolve
    trees = json.load(open(os.path.join(ROOT, "exports", "all_derivations.json"), encoding="utf8"))[args.dataset]
    ids = [t for t in trees if not args.only or t in args.only]
    out = os.path.join(ROOT, "benchmarks", "results", "lspec", f"specs_{args.dataset}.jsonl")
    done = set()
    if os.path.exists(out) and not args.no_lean:
        done = {json.loads(line)["id"] for line in open(out, encoding="utf8") if line.strip()}

    def run(lean):
        for task_id in ids:
            if task_id in done:
                continue
            started = time.time()
            try:
                row = check_task(resolve(task_id).load(task_id), lean)
            except Exception as error:
                row = {"id": task_id, "defs": 0, "verbatim": [], "same": 0,
                       "errors": [f"{type(error).__name__}: {str(error)[:300]}"]}
            row["seconds"] = round(time.time() - started, 1)
            if lean is not None:
                ok = not row["errors"]
                print(f"{task_id:32s} {'SAME' if ok else 'DIFF'}  defs {row['defs']}  same {row['same']}  "
                      f"lean-only {len(row['verbatim'])}  {'' if ok else str(row['errors'][0])[:200]!r}", flush=True)
                with open(out, "a", encoding="utf8") as handle:
                    handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    if args.no_lean:
        run(None)
        print(f"rendered {len(ids)} tasks to benchmarks/results/lspec/specs/")
        return
    from FormalLLM.lean.session import FULL_IMPORTS, LeanSession
    from lspec_equiv import control
    with LeanSession(imports=FULL_IMPORTS, startup_timeout=1200) as lean:
        control(lean)
        control_consts(lean)
        run(lean)
    rows = [json.loads(line) for line in open(out, encoding="utf8") if line.strip()]
    d = sum(r["defs"] for r in rows)
    print(f"{args.dataset}: {sum(r['same'] for r in rows)} of {d} definitions unchanged in meaning; "
          f"{sum(len(r['verbatim']) for r in rows)} commands left in Lean; "
          f"{sum(not r['errors'] for r in rows)} of {len(rows)} tasks fully checked")


if __name__ == "__main__":
    main()
