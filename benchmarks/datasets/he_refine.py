"""The paper's method on the HumanEval pilot subset: derive a verified program, then run the real tests.

For each problem in ``he_specs.SPECS`` (specifications validated against the reference solutions):

1. the model refines the specification step by step; every step is checked by the prover;
2. the finished derivation is emitted as Python (whole-number division where the types say so);
3. it is wrapped as the HumanEval function and run on the original tests ("base") and on
   EvalPlus' ~80x larger test set ("plus"), exactly as for the direct baseline.

    python -m benchmarks.datasets.he_refine --config gpt-oss-120b-low --repeats 3 --assist --out he_refine.jsonl
    python -m benchmarks.datasets.he_refine --summarize he_refine.jsonl --baseline direct_baseline.jsonl

Every row keeps the model's raw replies, so the derivation can be replayed offline. A run whose every
model call failed to connect is labelled NETWORK, shown but not counted as a failure; before it starts, one
tiny model call checks that the endpoint answers (``--no-preflight`` skips that).
"""
import argparse
import ast
import json
import os
import sys
import time
import traceback

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)


def function_parameters(task_id: str):
    from benchmarks.datasets import humaneval as he
    problem = he.load_problems()[task_id]
    for node in ast.walk(ast.parse(problem["prompt"])):
        if isinstance(node, ast.FunctionDef) and node.name == problem["entry_point"]:
            return [a.arg for a in node.args.args]
    raise ValueError(f"no definition of {problem['entry_point']} in the prompt of {task_id}")


def build_solution(task_id: str, program_python: str) -> str:
    """The HumanEval function around a derived program (bind lengths, run, return the result)."""
    from benchmarks.datasets import humaneval as he
    from benchmarks.datasets.he_specs import SPECS
    entry, problem = SPECS[task_id], he.load_problems()[task_id]
    params = function_parameters(task_id)
    lines = [f"def {problem['entry_point']}({', '.join(params)}):"]
    for spec_name, param in zip(entry["args"], params):
        if spec_name != param:
            lines.append(f"    {spec_name} = {param}")
    for name, expression in entry["bind"].items():
        lines.append(f"    {name} = {expression}")
    lines += ["    " + line for line in program_python.splitlines()]
    lines.append(f"    return {entry['result']}")
    return "\n".join(lines) + "\n"


def derive(task_id: str, provider, args):
    """Run the refiner on one specification; returns ``(outcome, detail, graph, engine, calls, seconds)``."""
    from benchmarks.harness import InstrumentedProvider
    from benchmarks.datasets.he_specs import SPECS
    from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
    from FormalLLM.llm.provider import LLMBudgetExhausted
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import RefinementEngine
    from FormalLLM.refinement.graph.graph import RefinementGraph
    from FormalLLM.verification.backends import get_backend

    inst = InstrumentedProvider(provider, args.budget)
    spec = parse_spec(SPECS[task_id]["spec"])
    graph = RefinementGraph(spec)
    engine = RefinementEngine(backend=get_backend(args.backend))
    refiner = AutomatedRefiner(engine, inst, max_retries=args.max_retries, max_depth=args.max_depth,
                               use_multi_turn=(args.turns == 2), assist=args.assist)
    started, outcome, detail = time.time(), "FAILED", ""
    try:
        ok = refiner.refine_node(graph, graph.root_id)
        outcome = "SUCCESS" if ok and graph.is_complete(graph.root_id) else "FAILED"
    except RefinementExhausted as error:
        outcome, detail = "EXHAUSTED", str(error)
    except LLMBudgetExhausted as error:
        outcome, detail = "BUDGET", str(error)
    except Exception as error:                                    # keep the study going
        outcome, detail = "ERROR", f"{type(error).__name__}: {error}\n{traceback.format_exc(limit=3)}"
    return outcome, detail, graph, engine, inst, time.time() - started, refiner


def run(args):
    from benchmarks import run_bench
    from benchmarks.datasets import humaneval as he
    from benchmarks.datasets.he_specs import SPECS
    from benchmarks.harness import program_to_str, summarise_graph
    from FormalLLM.llm.transport import NETWORK, effective_outcome, lost_to_network
    from FormalLLM.lpl.typed_python import python_for
    from FormalLLM.lspec.parser import parse_spec

    wanted = [t for t in SPECS if args.tasks in (None, ["all"]) or t in args.tasks
              or SPECS[t]["tier"] in args.tasks]
    cfg = run_bench.CONFIGS[args.config]
    done = set()
    if os.path.exists(args.out):
        with open(args.out, encoding="utf8") as handle:
            done = {(r["task_id"], r["repeat"]) for r in map(json.loads, filter(str.strip, handle))
                    if effective_outcome(r) != NETWORK}              # a run lost to the network is run again
    for task_id in wanted:
        for repeat in range(args.repeats):
            if (task_id, repeat) in done:
                continue
            provider = run_bench.make_provider(cfg, args.temperature, args.timeout)
            outcome, detail, graph, engine, inst, seconds, refiner = derive(task_id, provider, args)
            graph_summary = summarise_graph(graph)
            if outcome != "SUCCESS" and lost_to_network([c["response"] for c in inst.calls],
                                                        graph_summary["error_messages"]):
                outcome = NETWORK
                detail = "the model endpoint was unreachable on every call; not counted as a failure. " + detail
            row = {"task_id": task_id, "name": SPECS[task_id]["name"], "tier": SPECS[task_id]["tier"],
                   "repeat": repeat, "config": args.config, "outcome": outcome, "detail": detail,
                   "llm_calls": len(inst.calls), "wall_s": round(seconds, 1), "assist": args.assist,
                   "turns": args.turns, "max_retries": args.max_retries, "backend": args.backend,
                   "subtree_budget": refiner.subtree_budget,
                   "strict_variant": os.environ.get("FORMALLLM_STRICT_VARIANT", "1"),
                   "assist_discharges": refiner.assist_discharges, "program": None, "python": None,
                   "base": None, "plus": None, "certificate": None, "graph": graph_summary,
                   "raw_responses": [c["response"] for c in inst.calls]}
            if outcome == "SUCCESS":
                program = graph.reconstruct_program()
                row["program"] = program_to_str(program)
                try:
                    row["python"] = python_for(program, parse_spec(SPECS[task_id]["spec"]))
                except NotImplementedError as error:      # proved, but a test in it cannot be run
                    row["python"], row["detail"] = None, f"not executable: {error}"
                    row.update({"base": "not-executable", "plus": "not-executable"})
                else:
                    result = he.run_tests(task_id, build_solution(task_id, row["python"]), plus=True)
                    row.update({"base": result.base, "plus": result.plus})
                if args.certify:
                    try:
                        from FormalLLM.verification.backends import get_backend
                        from FormalLLM.verification.certify import certify_derivation
                        row["certificate"] = certify_derivation(graph, engine,
                                                                {name: get_backend(name) for name in args.certify})
                    except Exception as error:               # never lose a result to a certifier problem
                        row["certificate"] = {"error": f"{type(error).__name__}: {error}"}
            with open(args.out, "a", encoding="utf8") as handle:
                handle.write(json.dumps(row) + "\n")
            print(f"{task_id:14s} {row['name']:24s} repeat {repeat}: {outcome:8s} calls={row['llm_calls']:2d} "
                  f"{seconds:6.1f}s  base={row['base']} plus={row['plus']}", flush=True)
    summarize(args.out, getattr(args, "baseline", None))


def summarize(path, baseline_path=None):
    from FormalLLM.llm.transport import NETWORK, effective_outcome
    all_rows = [json.loads(line) for line in open(path, encoding="utf8") if line.strip()]
    lost = [r for r in all_rows if effective_outcome(r) == NETWORK]
    rows = [r for r in all_rows if effective_outcome(r) != NETWORK]
    baseline = {}
    if baseline_path and os.path.exists(baseline_path):
        for line in open(baseline_path, encoding="utf8"):
            if line.strip():
                r = json.loads(line)
                baseline[r["task_id"]] = (r.get("base_ok"), r.get("plus_ok"))
    tasks = sorted({r["task_id"] for r in rows}, key=lambda t: int(t.split("/")[1]))
    header = f"{'task':14s} {'problem':24s} {'tier':4s} {'derived':>9s} {'pass base':>10s} {'pass plus':>10s}"
    if baseline:
        header += f" {'direct base/plus':>17s}"
    print(header)
    total_runs = total_derived = total_plus = 0
    for task in tasks:
        mine = [r for r in rows if r["task_id"] == task]
        derived = [r for r in mine if r["outcome"] == "SUCCESS"]
        base = sum(1 for r in derived if r["base"] == "pass")
        plus = sum(1 for r in derived if r["plus"] == "pass")
        total_runs += len(mine)
        total_derived += len(derived)
        total_plus += plus
        line = (f"{task:14s} {mine[0]['name']:24s} {mine[0]['tier']:4s} {len(derived):>4d}/{len(mine):<4d} "
                f"{base:>5d}/{len(derived):<4d} {plus:>5d}/{len(derived):<4d}")
        if baseline and task in baseline:
            line += f" {str(baseline[task][0]):>8s}/{str(baseline[task][1]):<8s}"
        print(line)
    print(f"\n{total_derived} of {total_runs} runs derived a program; {total_plus} of those pass every "
          f"HumanEval and EvalPlus test. A derived program that fails a test points at the specification, "
          f"not the proof: look at the row's 'program'.")
    if lost:
        print(f"{len(lost)} further run(s) never reached the model (NETWORK) and are not counted above; "
              f"running the same command again repeats only the missing ones.")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", default="gpt-oss-120b-low")
    ap.add_argument("--tasks", nargs="*", default=None, help="task ids, tiers (A B C) or 'all'")
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--turns", type=int, choices=(1, 2), default=2)
    ap.add_argument("--budget", type=int, default=30)
    ap.add_argument("--max-retries", type=int, default=4)
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--assist", action="store_true")
    ap.add_argument("--strict", choices=("1", "0"), default=None)
    ap.add_argument("--backend", default="z3")
    ap.add_argument("--certify", nargs="*", default=None, choices=("coq", "lean"))
    ap.add_argument("--out", default="he_refine.jsonl")
    ap.add_argument("--baseline", default=None, help="a direct_baseline.jsonl to print next to the results")
    ap.add_argument("--summarize", metavar="FILE", default=None)
    ap.add_argument("--no-preflight", action="store_true",
                    help="skip the one-call check that the model endpoint answers before the run starts")
    args = ap.parse_args()
    if args.strict is not None:
        os.environ["FORMALLLM_STRICT_VARIANT"] = args.strict
    if args.summarize:
        summarize(args.summarize, args.baseline)
        return
    if not args.no_preflight:
        from benchmarks import reliability_batch
        reachable, note = reliability_batch.preflight(args)
        if not reachable:
            raise SystemExit(f"The model could not be reached ({note}). Nothing was started. Check the model "
                             "server, its tunnel and the internet, then run the same command again: finished "
                             "runs are kept.")
        print(f"model check: {note}", flush=True)
    run(args)


if __name__ == "__main__":
    main()
