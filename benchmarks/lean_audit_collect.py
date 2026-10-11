"""Phase 2 (step 1): collect the DISTINCT proof obligations of the stored successful derivations.

Replays every stored successful v8-code run offline (the model's stored replies, no network, no Lean), re-derives the
obligations of the final derivation exactly as ``certify_derivation`` does, and de-duplicates them by their Lean source.
Z3 accepted every one of them in the original run (that is how the step was kept); Coq's verdict per step is in the
stored certificate. Output: ``benchmarks/results/lean_audit/obligations.jsonl`` (one distinct obligation per line with the
source of the Lean theorem, how many derivations contain it, and the recorded Coq verdicts) and a summary.

    python benchmarks/lean_audit_collect.py [--limit N]
"""
import argparse
import collections
import contextlib
import glob
import hashlib
import io
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "benchmarks", "results", "lean_audit")

FILES = (glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v8_sqrt_assist_*.jsonl"))
         + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v7_sqrt_assist_20261005*.jsonl"))
         + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v8_sqrt_medium_*.jsonl"))
         + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v8cases_*.jsonl"))
         + glob.glob(os.path.join(ROOT, "benchmarks/results/reliability/v7cases_*.jsonl"))
         + [os.path.join(ROOT, "benchmarks/results/datasets", n)
            for n in ("he_refine_v8.jsonl", "he_refine_v8_heldout.jsonl", "he_refine_v7.jsonl")])


def spec_text(row, cases):
    if "case_id" in row:
        return cases[row["case_id"]]["spec"]
    from benchmarks.datasets.he_specs import SPECS
    return SPECS[row["task_id"]]["spec"]


def rebuild(row, cases):
    """The finished graph and engine of a stored successful run, re-derived from its replies."""
    from benchmarks.harness import InstrumentedProvider
    from FormalLLM.agent.refiner import AutomatedRefiner
    from FormalLLM.llm.provider import MockProvider
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import RefinementEngine
    from FormalLLM.refinement.graph.graph import RefinementGraph
    from FormalLLM.verification.backends import get_backend
    if row.get("strict_variant") in ("0", "1"):
        os.environ["FORMALLLM_STRICT_VARIANT"] = row["strict_variant"]
    replies = row.get("raw_responses") or []
    provider = InstrumentedProvider(MockProvider(list(replies)), budget=len(replies) or 1)
    engine = RefinementEngine(backend=get_backend(row.get("backend") or "z3"))
    refiner = AutomatedRefiner(engine, provider, max_retries=row.get("max_retries") or 4, max_depth=6,
                               use_multi_turn=((row.get("turns") or 2) == 2),
                               assist=bool(row.get("assist")), subtree_budget=row.get("subtree_budget", 10))
    graph = RefinementGraph(parse_spec(spec_text(row, cases)))
    with contextlib.redirect_stdout(io.StringIO()):
        ok = refiner.refine_node(graph, graph.root_id)
    return graph, engine, ok and graph.is_complete(graph.root_id)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None, help="only the first N successful runs (for a quick check)")
    args = ap.parse_args()
    from benchmarks.cases import CASES
    from FormalLLM.llm.transport import NETWORK, effective_outcome
    from FormalLLM.verification.backends import get_backend
    from FormalLLM.verification.certify import derivation_obligations
    lean = get_backend("lean")
    cases = {c["id"]: c for c in CASES}
    distinct = collections.OrderedDict()
    runs = failed_replays = unsupported = total = 0
    for path in FILES:
        for line in open(path, encoding="utf8"):
            if not line.strip():
                continue
            row = json.loads(line)
            if effective_outcome(row) == NETWORK or row["outcome"] != "SUCCESS":
                continue
            if args.limit and runs >= args.limit:
                break
            runs += 1
            try:
                graph, engine, complete = rebuild(row, cases)
            except Exception:
                complete = False
            if not complete:
                failed_replays += 1
                continue
            coq_failed = {(f["node"], f["law"]) for f in ((row.get("certificate") or {}).get("coq") or {}).get("failures", [])}
            for item in derivation_obligations(graph, engine):
                total += 1
                try:
                    source = lean.theorem_text(item["obligation"])
                except Exception:
                    unsupported += 1
                    source = None
                key = hashlib.sha256((source or repr(item["obligation"])).encode("utf8")).hexdigest()[:16]
                entry = distinct.setdefault(key, {"key": key, "law": item["law"], "lean_source": source,
                                                  "description": getattr(item["obligation"], "description", ""),
                                                  "derivations": 0, "coq_failed_in": 0,
                                                  "example": os.path.basename(path)})
                entry["derivations"] += 1
                entry["coq_failed_in"] += (item["node"], item["law"]) in coq_failed
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "obligations.jsonl"), "w", encoding="utf8") as handle:
        for entry in distinct.values():
            handle.write(json.dumps(entry) + "\n")
    laws = collections.Counter(e["law"] for e in distinct.values())
    summary = {"successful_runs_read": runs, "replays_not_reproduced": failed_replays, "obligations_total": total,
               "distinct": len(distinct), "not_translatable_to_lean": sum(1 for e in distinct.values() if e["lean_source"] is None),
               "distinct_by_law": dict(laws)}
    json.dump(summary, open(os.path.join(OUT, "collect_summary.json"), "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
