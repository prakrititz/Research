"""Audit the stored runs offline: replay every successful row, then re-check it independently of the original run.

A result row keeps the model's raw replies, so the engine can be run again on exactly those replies, with no model
and no network (``replay.py`` does this and compares the outcome). This tool replays every SUCCESS row of the given
result files and then asks Z3 two questions the original run did not ask.

  loops   For every loop the model proposed in a successful run, accepted or refused: does

              invariant /\\ guard  =>  0 <= variant

          hold, i.e. can the loop measure never be negative while the loop runs? (This is the extra obligation of the
          v9 termination rule.) With ``--strict 1`` the rows are replayed under the old strict rule (``0 <= V < V0``
          after every pass) instead, and the tool reports which rows no longer replay as recorded.

  steps   For every step of every finished derivation (found by the model or by the leaf assist): do the step's proof
          obligations still come out PROVED in a fresh Z3 run? A step that Z3 now refutes was accepted wrongly.

    python benchmarks/audit_stored_runs.py loops
    python benchmarks/audit_stored_runs.py loops --strict 1
    python benchmarks/audit_stored_runs.py steps --workers 2
    python benchmarks/audit_stored_runs.py steps benchmarks/results/datasets/he_refine_v8.jsonl

Without file arguments it reads every reliability file and every HumanEval pilot file under ``benchmarks/results``.
A full pass takes about 10 minutes per mode on two cores; ``--workers N`` runs N processes. Rows recorded with older
code may legitimately not replay as recorded, and so may the few rows whose quantified goals sit at the edge of what
Z3 decides within the leaf assist's time limits (a busy machine tips them); the report lists such rows instead of
hiding them, and a re-run can differ by a row or two there. Only Z3 is used (no Coq, no Lean), so rows recorded with
another backend are replayed with Z3.
"""
import argparse
import collections
import contextlib
import copy
import glob
import io
import json
import multiprocessing
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

LOOP_LAWS = ("initialised_iteration", "iteration")


def default_files():
    results = os.path.join(ROOT, "benchmarks", "results")
    return (sorted(glob.glob(os.path.join(results, "reliability", "*.jsonl")))
            + sorted(glob.glob(os.path.join(results, "datasets", "he_refine_*.jsonl"))))


def mentions_a_loop(row):
    return any(("variant" in reply.lower() or "iteration" in reply.lower())
               for reply in (row.get("raw_responses") or []) if isinstance(reply, str))


def replay(row, force_strict=None):
    """Replay one row with the engine; returns (graph, outcome, LLM calls used, program, engine)."""
    from benchmarks.cases import CASES
    from benchmarks.harness import InstrumentedProvider, program_to_str
    from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
    from FormalLLM.llm.provider import LLMBudgetExhausted, MockProvider
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import RefinementEngine
    from FormalLLM.refinement.graph.graph import RefinementGraph
    from FormalLLM.verification.backends import get_backend

    if "case_id" in row:
        spec_text = {c["id"]: c for c in CASES}[row["case_id"]]["spec"]
    else:
        from benchmarks.datasets.he_specs import SPECS
        spec_text = SPECS[row["task_id"]]["spec"]
    if row.get("strict_variant") in ("0", "1"):
        os.environ["FORMALLLM_STRICT_VARIANT"] = row["strict_variant"]
    if force_strict in ("0", "1"):
        os.environ["FORMALLLM_STRICT_VARIANT"] = force_strict
    replies = row.get("raw_responses") or []
    provider = InstrumentedProvider(MockProvider(list(replies)), budget=len(replies) or 1)
    engine = RefinementEngine(backend=get_backend("z3"))
    refiner = AutomatedRefiner(engine, provider, max_retries=row.get("max_retries") or 4, max_depth=6,
                               use_multi_turn=((row.get("turns") or 2) == 2), assist=bool(row.get("assist")),
                               subtree_budget=row.get("subtree_budget", 10))
    graph = RefinementGraph(parse_spec(spec_text))
    outcome, program = "FAILED", None
    try:
        if refiner.refine_node(graph, graph.root_id) and graph.is_complete(graph.root_id):
            outcome, program = "SUCCESS", program_to_str(graph.reconstruct_program())
    except RefinementExhausted:
        outcome = "EXHAUSTED"
    except LLMBudgetExhausted:
        outcome = "BUDGET"
    return graph, outcome, len(provider.calls), program, engine


def render(expr):
    from FormalLLM.llm import spec_render as sr
    try:
        return sr.render_expr(expr)
    except Exception as error:                   # never lose a record over a rendering problem
        return f"<unrenderable: {error}>"


def bounded_obligation(spec, law, params):
    """I /\\ G => 0 <= V, with I as the engine builds it (rigid facts of the specification included)."""
    from FormalLLM.lspec.ast import BinaryOp, Number
    from FormalLLM.refinement.frame import obligation_params, rigid_context
    from FormalLLM.verification.proof_obligations import ProofObligation

    if law == "iteration":
        invariant = spec.precondition.expr
    else:
        invariant = rigid_context(spec, params["invariant"]) if params.get("invariant") is not None else None
    if invariant is None:
        return None
    return ProofObligation(assumptions=[copy.deepcopy(invariant), copy.deepcopy(params["guard"])],
                           goal=BinaryOp(Number("0"), "<=", copy.deepcopy(params["variant"])),
                           params=obligation_params(spec),
                           description="the measure must not be negative while the loop runs: I /\\ G => 0 <= V")


def ask(obligation, quick_ms):
    """PROVED / FAILED / UNKNOWN; a patient run only when the quick one could not decide."""
    from FormalLLM.verification import z3_backend as zb
    started = time.time()
    status, message = zb.verify_obligation(obligation, quick_ms)          # None: the engine's own plan
    if status == zb.VerificationResult.UNKNOWN:
        status, message = zb.verify_obligation(obligation, 30000)
    return status, message, round(time.time() - started, 2)


def audit_loops(path, index, row, force_strict):
    from FormalLLM.refinement.graph.status import AttemptStatus
    from FormalLLM.refinement.vocabulary import unknown_names
    started = time.time()
    with contextlib.redirect_stdout(io.StringIO()):
        graph, outcome, calls, program, _engine = replay(row, force_strict)
    reproduced = (outcome == row["outcome"] and calls == row["llm_calls"]
                  and (program == row.get("program") or row["outcome"] != "SUCCESS"))
    records = []
    for attempt in graph.attempts.values():
        if attempt.law not in LOOP_LAWS:
            continue
        params = attempt.parameters or {}
        spec = graph.nodes[attempt.source_node_id].specification
        record = {"file": os.path.basename(path), "row": index, "kind": "loop", "attempt": attempt.id,
                  "law": attempt.law, "status": attempt.status.value,
                  "in_final": bool(outcome == "SUCCESS" and attempt.status == AttemptStatus.ACCEPTED
                                   and graph.is_live(attempt.source_node_id))}
        if params.get("guard") is None or params.get("variant") is None:
            record["bounded"] = "NOPARAMS"
        elif force_strict is None:
            obligation = bounded_obligation(spec, attempt.law, params)
            record.update(guard=render(params["guard"]), variant=render(params["variant"]),
                          invariant=render(params.get("invariant")) if params.get("invariant") is not None else None)
            try:
                record["invented"] = list(unknown_names(spec, params))
                if obligation is None:
                    record["bounded"] = "NOINVARIANT"
                else:
                    status, message, seconds = ask(obligation, 5000)
                    record.update(bounded=status, seconds=seconds)
                    if status == "FAILED":
                        record["counterexample"] = message[:400]
            except Exception as error:
                record["bounded"] = f"ERROR: {type(error).__name__}: {error}"[:200]
        records.append(record)
    summary = {"file": os.path.basename(path), "row": index, "kind": "row", "replayed": outcome,
               "reproduced": bool(reproduced), "strict_recorded": row.get("strict_variant"),
               "seconds": round(time.time() - started, 1)}
    return summary, records


def audit_steps(path, index, row):
    from FormalLLM.refinement.graph.status import AttemptStatus
    from FormalLLM.verification import z3_backend as zb
    started = time.time()
    with contextlib.redirect_stdout(io.StringIO()):
        graph, outcome, calls, program, engine = replay(row)
    reproduced = (outcome == row["outcome"] and calls == row["llm_calls"]
                  and (program == row.get("program") or row["outcome"] != "SUCCESS"))
    records = []
    if outcome == "SUCCESS":
        for attempt in graph.attempts.values():
            if attempt.status != AttemptStatus.ACCEPTED or not graph.is_live(attempt.source_node_id):
                continue
            spec = graph.nodes[attempt.source_node_id].specification
            record = {"file": os.path.basename(path), "row": index, "kind": "step", "attempt": attempt.id,
                      "law": attempt.law, "source": getattr(attempt, "source", "model"), "verdicts": []}
            try:
                for obligation in engine.laws[attempt.law]().apply(spec, attempt.parameters or {}).obligations:
                    status, message, seconds = ask(obligation, None)
                    record["verdicts"].append(status)
                    if status == zb.VerificationResult.FAILED:
                        record["refuted"] = {"goal": render(obligation.goal), "message": message[:400]}
                    elif status == zb.VerificationResult.UNKNOWN:
                        record["undecided"] = {"goal": render(obligation.goal)[:300]}
            except Exception as error:
                record["error"] = f"{type(error).__name__}: {error}"[:200]
            records.append(record)
    summary = {"file": os.path.basename(path), "row": index, "kind": "row", "replayed": outcome,
               "reproduced": bool(reproduced), "strict_recorded": row.get("strict_variant"),
               "seconds": round(time.time() - started, 1)}
    return summary, records


def work(task):
    mode, path, index, force_strict = task
    with open(path, encoding="utf8") as handle:
        row = [json.loads(line) for line in handle if line.strip()][index]
    try:
        if mode == "loops":
            return audit_loops(path, index, row, force_strict)
        return audit_steps(path, index, row)
    except Exception as error:
        return {"file": os.path.basename(path), "row": index, "kind": "row", "reproduced": False,
                "error": f"{type(error).__name__}: {error}"[:200]}, []


def report_loops(rows, records, force_strict):
    if force_strict is not None:
        recorded = [r for r in rows if r.get("strict_recorded") != force_strict]
        same = sum(1 for r in recorded if r["reproduced"])
        print(f"\nrows recorded under the other termination rule: {len(recorded)}; replay as recorded under the "
              f"strict={force_strict} rule: {same}; do not: {len(recorded) - same}")
        by_file = collections.Counter(r["file"] for r in recorded if not r["reproduced"])
        for name, n in sorted(by_file.items()):
            print(f"    {n:4d} of {sum(1 for r in recorded if r['file'] == name):4d}  {name}")
        return
    checked = [r for r in records if r["bounded"] not in ("NOPARAMS", "NOINVARIANT")]
    print(f"\n{len(rows)} successful rows replayed ({sum(1 for r in rows if r['reproduced'])} exactly as recorded); "
          f"{len(records)} loop attempts, {len(records) - len(checked)} without a guard or measure")
    print("verdict on  I /\\ G => 0 <= V :", dict(collections.Counter(r["bounded"] for r in checked)))
    accepted = [r for r in checked if r["in_final"]]
    print(f"loops in a finished derivation: {len(accepted)}, bounded: "
          f"{sum(1 for r in accepted if r['bounded'] == 'PROVED')}")
    for r in checked:
        if r["bounded"] != "PROVED":
            print(f"  NOT BOUNDED  {r['file']} row {r['row']} {r['law']} {r['status']}"
                  f"{' (in the final derivation)' if r['in_final'] else ''}: invariant {r.get('invariant')} | "
                  f"guard {r.get('guard')} | variant {r.get('variant')}")


def report_steps(rows, records):
    print(f"\n{len(rows)} successful rows replayed ({sum(1 for r in rows if r['reproduced'])} exactly as recorded); "
          f"{len(records)} steps in finished derivations")
    print("  by law   :", dict(collections.Counter(r["law"] for r in records)))
    print("  by source:", dict(collections.Counter(r["source"] for r in records)))
    verdicts = collections.Counter(v for r in records for v in r["verdicts"])
    print("obligations put to a fresh Z3:", dict(verdicts))
    for r in records:
        if "refuted" in r:
            print(f"  REFUTED   {r['file']} row {r['row']} {r['law']} ({r['source']}): {r['refuted']['goal']}")
        if "undecided" in r:
            print(f"  UNDECIDED {r['file']} row {r['row']} {r['law']} ({r['source']}): {r['undecided']['goal']}")
        if "error" in r:
            print(f"  ERROR     {r['file']} row {r['row']} {r['law']}: {r['error']}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=("loops", "steps"))
    ap.add_argument("files", nargs="*", help="result files (.jsonl); default: all reliability and pilot files")
    ap.add_argument("--strict", choices=("0", "1"), default=None,
                    help="loops only: replay under this termination rule instead of the recorded one")
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--out", default=None, help="also write every record to this .jsonl file")
    args = ap.parse_args()

    tasks = []
    for path in [os.path.abspath(p) for p in (args.files or default_files())]:
        with open(path, encoding="utf8") as handle:
            for index, line in enumerate(handle):
                if not line.strip():
                    continue
                row = json.loads(line)
                if row.get("outcome") == "SUCCESS" and (args.mode == "steps" or mentions_a_loop(row)):
                    tasks.append((args.mode, path, index, args.strict))
    print(f"{args.mode}: {len(tasks)} successful rows to replay with {args.workers} worker(s)", flush=True)

    rows, records, out = [], [], (open(args.out, "w", encoding="utf8") if args.out else None)
    runner = (multiprocessing.Pool(args.workers).imap_unordered(work, tasks) if args.workers > 1
              else map(work, tasks))
    for done, (summary, found) in enumerate(runner, 1):
        rows.append(summary)
        records.extend(found)
        if out:
            for record in found + [summary]:
                out.write(json.dumps(record) + "\n")
        quiet = args.mode == "loops" and args.strict is not None       # here a changed replay is the expected answer
        if not quiet and (not summary["reproduced"] or any(r.get("bounded") not in (None, "PROVED", "NOPARAMS")
                                                           or "refuted" in r or "undecided" in r for r in found)):
            print(f"  [{done}/{len(tasks)}] {summary['file']} row {summary['row']}: "
                  f"{'not replayed as recorded' if not summary['reproduced'] else 'replayed as recorded'}"
                  f"{', ' + summary['error'] if summary.get('error') else ''}", flush=True)
        elif done % 50 == 0:
            print(f"  [{done}/{len(tasks)}]", flush=True)
    if out:
        out.close()
    (report_loops(rows, records, args.strict) if args.mode == "loops" else report_steps(rows, records))
    if args.mode == "loops" and args.strict is None or args.mode == "steps":
        different = [r for r in rows if not r["reproduced"]]
        print(f"\nrows that did not replay as recorded: {len(different)}")
        for r in sorted(different, key=lambda r: (r["file"], r["row"]))[:40]:
            print(f"    {r['file']} row {r['row']} (replayed {r.get('replayed')})")


if __name__ == "__main__":
    main()
