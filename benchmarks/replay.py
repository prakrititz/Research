"""Replay stored results offline: same model replies in, same derivation out.

A language model is not reproducible -- ask it twice and the answers differ. What *can* be
reproduced exactly is everything after the model: the same replies, fed back to the same
code, must give the same sequence of accepted and refused steps, the same program, and
the same proof-assistant verdicts. This tool does that for any result file written by
``benchmarks/reliability.py`` or ``benchmarks/run_bench.py`` (each row keeps the model's
raw replies), with no network access and no credentials.

    python benchmarks/replay.py benchmarks/results/reliability/v5_relaxed_assist_*.jsonl
    python benchmarks/replay.py RESULTS.jsonl --rows 0 3 --certify coq lean

For every row it reports whether the replay reproduced the recorded outcome, the number of
LLM calls consumed and the final program. A row recorded with older code may legitimately
differ; the report says so instead of hiding it.
"""
import argparse
import contextlib
import glob
import io
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def load_rows(paths, wanted):
    rows = []
    for pattern in paths:
        for path in sorted(glob.glob(pattern)) or [pattern]:
            with open(path, encoding="utf8") as handle:
                for index, line in enumerate(handle):
                    if line.strip() and (not wanted or index in wanted):
                        rows.append((path, index, json.loads(line)))
    return rows


def replay_row(row, cases, args):
    from benchmarks.harness import InstrumentedProvider, program_to_str
    from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
    from FormalLLM.llm.provider import LLMBudgetExhausted, MockProvider
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import RefinementEngine
    from FormalLLM.refinement.graph.graph import RefinementGraph

    if "case_id" in row:
        spec_text = cases[row["case_id"]]["spec"]
    else:                                              # a HumanEval pilot row (he_refine.py)
        from benchmarks.datasets.he_specs import SPECS
        spec_text = SPECS[row["task_id"]]["spec"]
    if row.get("strict_variant") in ("0", "1"):
        os.environ["FORMALLLM_STRICT_VARIANT"] = row["strict_variant"]
    replies = row.get("raw_responses") or []
    provider = InstrumentedProvider(MockProvider(list(replies)), budget=len(replies) or 1)
    from FormalLLM.verification.backends import get_backend
    engine = RefinementEngine(backend=get_backend(row.get("backend") or "z3"))
    # what the row itself recorded wins over the command line
    assist = row["assist"] if row.get("assist") is not None else args.assist
    refiner = AutomatedRefiner(engine, provider, max_retries=row.get("max_retries") or args.max_retries,
                               max_depth=args.max_depth,
                               use_multi_turn=((row.get("turns") or args.turns) == 2), assist=assist,
                               subtree_budget=row.get("subtree_budget", 10))
    graph = RefinementGraph(parse_spec(spec_text))
    outcome, program = "FAILED", None
    try:
        ok = refiner.refine_node(graph, graph.root_id)
        if ok and graph.is_complete(graph.root_id):
            outcome, program = "SUCCESS", program_to_str(graph.reconstruct_program())
    except RefinementExhausted:
        outcome = "EXHAUSTED"
    except LLMBudgetExhausted:
        outcome = "BUDGET"
    certificate = None
    if args.certify and outcome == "SUCCESS":
        from FormalLLM.verification.backends import get_backend
        from FormalLLM.verification.certify import certify_derivation
        certificate = certify_derivation(graph, engine, {name: get_backend(name) for name in args.certify})
    return outcome, len(provider.calls), program, certificate


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("results", nargs="+", help="result file(s) (.jsonl); wildcards allowed")
    ap.add_argument("--rows", nargs="*", type=int, default=None, help="only these row numbers")
    ap.add_argument("--turns", type=int, choices=(1, 2), default=2)
    ap.add_argument("--max-retries", type=int, default=4)
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--assist", action="store_true", help="the rows were recorded with the leaf assist on")
    ap.add_argument("--strict", choices=("1", "0"), default=None, help="termination rule the rows were recorded under")
    ap.add_argument("--certify", nargs="*", default=None, choices=("coq", "lean"))
    args = ap.parse_args()

    if args.strict is not None:
        os.environ["FORMALLLM_STRICT_VARIANT"] = args.strict
    from benchmarks.cases import CASES
    cases = {c["id"]: c for c in CASES}

    from FormalLLM.llm.transport import NETWORK, effective_outcome
    same = differ = 0
    for path, index, row in load_rows(args.results, set(args.rows or [])):
        if effective_outcome(row) == NETWORK:                    # the model never answered: nothing to replay
            print(f"{os.path.basename(path)}[{index}]  recorded as lost to the network  -> skipped")
            continue
        with contextlib.redirect_stdout(io.StringIO()):          # the refiner narrates every step
            outcome, calls, program, certificate = replay_row(row, cases, args)
        reproduced = (outcome == row["outcome"] and calls == row["llm_calls"]
                      and (program == row.get("program") or row["outcome"] != "SUCCESS"))
        same += reproduced
        differ += not reproduced
        mark = "same" if reproduced else "DIFFERENT"
        line = (f"{os.path.basename(path)}[{index}]  recorded {row['outcome']}/{row['llm_calls']} calls, "
                f"replayed {outcome}/{calls} calls  -> {mark}")
        if certificate:
            line += "  | " + ", ".join(f"{name}: {data['certified']}/{certificate['obligations']}"
                                       for name, data in certificate.items() if name != "obligations")
        print(line)
    print(f"\n{same} of {same + differ} rows reproduced exactly.")
    return 0 if differ == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
