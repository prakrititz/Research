"""Command line for the Lean core.

    python -m FormalLLM.lean show   benchmarks/datasets/lean_specs/he_060_sum_to_n
    python -m FormalLLM.lean check  benchmarks/datasets/lean_specs/he_060_sum_to_n tree.json [--source]
    python -m FormalLLM.lean oracle he_060_sum_to_n [--source]          # the hand-written derivation of a library or Verina task
    python -m FormalLLM.lean solve  benchmarks/datasets/lean_specs/he_060_sum_to_n --config ornith [--budget 30]

``show`` prints what the engine sees (signature, definitions, the root goal); ``check`` applies a derivation written as JSON
(the format of ``laws.py``: ``{"law": "loop", ..., "children": [...]}``) and reports every step, then certifies it; ``oracle``
does the same for the derivations in ``benchmarks/datasets/lean_oracle.py`` and ``verina_oracle.py``; ``solve`` runs the model-driven
agent (needs a configured model, see ``benchmarks/run_bench.py``).
"""
import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def _task(path: str):
    from FormalLLM.lean.task import LeanTask
    return LeanTask.from_dir(path)


def _session(imports: str):
    from FormalLLM.lean.session import DEFAULT_IMPORTS, FULL_IMPORTS, LeanSession
    return LeanSession(imports=FULL_IMPORTS if imports == "full" else DEFAULT_IMPORTS, startup_timeout=1200)


def show(args) -> int:
    task = _task(args.task)
    print(f"{task.name}({', '.join(f'{n} : {t}' for n, t in task.params)}) : {task.ret}\n")
    print(task.description[:1500], "\n")
    print("--- definitions the engine sees ---")
    print(task.prelude.strip(), "\n")
    print("--- root goal ---")
    print(f"context: {task.binders()}\nfind ρ : {task.ret} such that {task.root_post.replace('⟪r⟫', 'ρ')}")
    print(f"\n{len(task.tests)} tests in test.json")
    return 0


def _report(derivation, steps, show_source: bool) -> int:
    for number, step in enumerate(steps, 1):
        print(f"step {number}: {step.status}" + (f" ({len(step.subgoals)} new goals)" if step.ok else ""))
        if not step.ok:
            print(step.feedback())
    if not derivation.complete:
        print(f"\nnot complete: open goals {[g.id for g in derivation.open_goals()]}")
        return 1
    certificate = derivation.certify()
    print(f"\ncertificate: compiles={certificate.compiles} axioms=[{certificate.axioms}] tests {certificate.passed}/{certificate.tests} "
          f"({certificate.seconds}s)")
    for error in certificate.errors:
        print("  error:", error[:300])
    if show_source:
        print("\n" + derivation.source())
    return 0 if certificate.verified else 1


def check(args) -> int:
    from FormalLLM.lean.engine import Derivation
    task = _task(args.task)
    tree = json.load(open(args.tree, encoding="utf8"))
    with _session(args.imports) as lean:
        derivation = Derivation(task, lean)
        return _report(derivation, derivation.apply_tree(tree), args.source)


def oracle(args) -> int:
    from benchmarks.datasets import lean_oracle, verina_oracle
    from FormalLLM.lean.engine import Derivation
    if args.id in lean_oracle.ORACLES:
        tree, library = lean_oracle.ORACLES[args.id], lean_oracle.LIBRARY
    elif args.id in verina_oracle.ORACLES:
        tree, library = verina_oracle.ORACLES[args.id], verina_oracle.DATASET
    else:
        print(f"no hand-written derivation for {args.id}")
        return 2
    task = _task(os.path.join(library, args.id))
    with _session(args.imports) as lean:
        derivation = Derivation(task, lean)
        return _report(derivation, derivation.apply_tree(tree), args.source)


def solve(args) -> int:
    from benchmarks import run_bench
    from FormalLLM.lean.agent import LeanAgent
    task = _task(args.task)
    cfg = run_bench.CONFIGS[args.config]
    provider = run_bench.make_provider(cfg, args.temperature, args.timeout)
    if cfg["kind"] == "ollama":
        provider.response_format = "json"
    with _session(args.imports) as lean:
        result = LeanAgent(provider, max_calls=args.budget).solve(task, lean)
    print(f"\noutcome {result.outcome}, verified {result.verified}, {len(result.calls)} calls, {result.retractions} retractions")
    if result.detail:
        print(result.detail)
    if args.source and result.derivation.complete:
        print("\n" + result.derivation.source())
    return 0 if result.verified else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="python -m FormalLLM.lean", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    s = sub.add_parser("show")
    s.add_argument("task")
    for name in ("check", "oracle", "solve"):
        p = sub.add_parser(name)
        if name == "check":
            p.add_argument("task")
            p.add_argument("tree")
        elif name == "oracle":
            p.add_argument("id")
        else:
            p.add_argument("task")
            p.add_argument("--config", default="gpt-oss-120b-low")
            p.add_argument("--budget", type=int, default=30)
            p.add_argument("--temperature", type=float, default=0.2)
            p.add_argument("--timeout", type=int, default=900)
        p.add_argument("--imports", choices=["default", "full"], default="default")
        p.add_argument("--source", action="store_true", help="print the Lean file of the finished derivation")
    args = ap.parse_args(argv)
    return {"show": show, "check": check, "oracle": oracle, "solve": solve}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
