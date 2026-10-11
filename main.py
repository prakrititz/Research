"""Derive a verified program from a specification, end to end.

    python main.py --case C5-sqrt-paper --config gpt-oss-120b-low --assist --certify coq lean

What happens, in order:

1. The specification (a built-in ``--case``, a ``--spec`` file, or ``--spec-text``) is parsed.
2. A language model proposes refinement steps -- the law, then its parameters -- and the
   prover checks every proof condition (``--backend``, Z3 by default). Rejected steps come back
   to the model with a counterexample.
3. The finished derivation is printed as an executable program.
4. ``--certify`` asks Coq and/or Lean to re-check every proof obligation of the derivation that
   was actually used (their kernels, not Z3, have the last word).

The hosted model's login is read from the environment (``FORMALLLM_REMOTE_AUTH``,
``user:password``); it is never taken from, or written to, a file in this repository.
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def parse_inputs(text):
    """``"N=10,e=1"`` -> ``{"N": 10, "e": 1}`` (numbers only; ``0.5`` gives a float)."""
    values = {}
    for part in filter(None, (p.strip() for p in text.split(","))):
        name, _, value = part.partition("=")
        number = float(value)
        values[name.strip()] = int(number) if number.is_integer() and "." not in value else number
    return values


def run_program(code, inputs, outputs):
    """Run the emitted Python on ``inputs``; return the final values of ``outputs``."""
    namespace = dict(inputs)
    exec(compile(code, "<derived program>", "exec"), {"__builtins__": {}}, namespace)
    return {name: namespace.get(name) for name in outputs}


def main(argv=None):
    from benchmarks.cases import CASES
    from benchmarks import run_bench

    cases = {c["id"]: c for c in CASES}
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    source = ap.add_argument_group("specification (default: the paper's square-root example)")
    source.add_argument("--case", default=None, help="a built-in case id (see --list-cases)")
    source.add_argument("--spec", default=None, help="a file containing an L_spec specification")
    source.add_argument("--spec-text", default=None, help="the specification as a string")
    source.add_argument("--list-cases", action="store_true")
    model = ap.add_argument_group("model")
    model.add_argument("--config", default="gpt-oss-120b-low", help="a name from benchmarks/run_bench.py CONFIGS")
    model.add_argument("--temperature", type=float, default=0.2)
    model.add_argument("--timeout", type=int, default=900, help="seconds per LLM call")
    search = ap.add_argument_group("search")
    search.add_argument("--turns", type=int, choices=(1, 2), default=2,
                        help="2 = law first, then its parameters (the paper's Algorithm 1)")
    search.add_argument("--budget", type=int, default=30, help="LLM calls allowed")
    search.add_argument("--max-retries", type=int, default=4)
    search.add_argument("--max-depth", type=int, default=6)
    search.add_argument("--assist", action="store_true",
                        help="let the prover close one-line leaves and report missing invariant facts (not in the paper)")
    search.add_argument("--strict", choices=("1", "0"), default=None,
                        help="1: a loop variant must also stay >= 0; 0: it must only decrease (the paper's Lemma 6.7)")
    proof = ap.add_argument_group("proofs")
    proof.add_argument("--backend", default="z3", help="z3 (default), coq, lean, cross-coq or cross-lean")
    proof.add_argument("--certify", nargs="*", default=None, choices=("coq", "lean"),
                       help="after success, have these proof assistants re-check the derivation")
    proof.add_argument("--proofs", default=None, help="directory to keep the generated Coq/Lean files in")
    out = ap.add_argument_group("output")
    out.add_argument("--run", default=None, metavar="N=10,e=1", help="execute the derived program on these inputs")
    out.add_argument("--json", default=None, help="write a machine-readable summary to this file")
    out.add_argument("--quiet", action="store_true", help="hide the model transcripts")
    args = ap.parse_args(argv)

    if args.list_cases:
        for case_id, case in cases.items():
            print(f"{case_id:22s} {case['title']}")
        return 0

    if args.strict is not None:
        os.environ["FORMALLLM_STRICT_VARIANT"] = args.strict
    if args.proofs:
        os.environ["FORMALLLM_PROOF_DIR"] = os.path.abspath(args.proofs)

    # Imported after the environment is set: the laws read it when they run.
    from FormalLLM.agent.refiner import AutomatedRefiner, RefinementExhausted
    from FormalLLM.llm import spec_render as sr
    from FormalLLM.llm.provider import LLMBudgetExhausted
    from FormalLLM.lpl.to_python import to_python
    from FormalLLM.lspec.parser import parse_spec
    from FormalLLM.refinement.engine import RefinementEngine
    from FormalLLM.refinement.graph.graph import RefinementGraph
    from FormalLLM.trace.serializer import export_graph_text
    from FormalLLM.verification.backends import get_backend
    from FormalLLM.verification.certify import certify_derivation, render_report
    from benchmarks.harness import InstrumentedProvider, program_to_str

    if args.spec_text:
        spec_text, title = args.spec_text, "(from --spec-text)"
    elif args.spec:
        with open(args.spec, encoding="utf8") as handle:
            spec_text, title = handle.read(), args.spec
    else:
        case_id = args.case or "C5-sqrt-paper"
        if case_id not in cases:
            raise SystemExit(f"unknown case {case_id!r}; try --list-cases")
        spec_text, title = cases[case_id]["spec"], f"{case_id}: {cases[case_id]['title']}"

    spec = parse_spec(spec_text)
    print(f"Specification  {title}\n")
    print(sr.render_spec(spec))

    if args.config not in run_bench.CONFIGS:
        raise SystemExit(f"unknown config {args.config!r}; known: {sorted(run_bench.CONFIGS)}")
    provider = InstrumentedProvider(
        run_bench.make_provider(run_bench.CONFIGS[args.config], args.temperature, args.timeout), args.budget)
    engine = RefinementEngine(backend=get_backend(args.backend))
    refiner = AutomatedRefiner(engine, provider, max_retries=args.max_retries, max_depth=args.max_depth,
                               use_multi_turn=(args.turns == 2), assist=args.assist)
    graph = RefinementGraph(spec)

    print(f"\nModel {args.config} | prover {engine.backend.name} | assist {'on' if args.assist else 'off'} "
          f"| budget {args.budget} calls\n")
    started = time.time()
    outcome, detail = "FAILED", ""
    try:
        if args.quiet:
            import contextlib
            with open(os.devnull, "w", encoding="utf8") as sink, contextlib.redirect_stdout(sink):
                ok = refiner.refine_node(graph, graph.root_id)
        else:
            ok = refiner.refine_node(graph, graph.root_id)
        outcome = "SUCCESS" if ok and graph.is_complete(graph.root_id) else "FAILED"
    except RefinementExhausted as error:
        outcome, detail = "EXHAUSTED", str(error)
    except LLMBudgetExhausted as error:
        outcome, detail = "BUDGET", str(error)
    seconds = time.time() - started

    summary = {"specification": title, "config": args.config, "backend": engine.backend.name,
               "outcome": outcome, "llm_calls": len(provider.calls), "assist_discharges": refiner.assist_discharges,
               "seconds": round(seconds, 1)}
    print("\n" + "=" * 78)
    print(f"{outcome}: {len(provider.calls)} LLM call(s), {refiner.assist_discharges} step(s) closed by the "
          f"prover alone, {seconds:.0f} s")
    if detail:
        print(detail)
    if outcome != "SUCCESS":
        print("\nDerivation so far:\n" + export_graph_text(graph))
        if args.json:
            with open(args.json, "w", encoding="utf8") as handle:
                json.dump(summary, handle, indent=2)
        return 1

    program = graph.reconstruct_program()
    code = to_python(program)
    summary["program"] = program_to_str(program)
    print("\nDerived program (every step proved):\n")
    print(program_to_str(program))
    print("\nAs Python:\n")
    print(code)

    if args.run:
        outputs = sorted(spec_frame_names(spec))
        result = run_program(code, parse_inputs(args.run), outputs)
        summary["run"] = {"inputs": args.run, "outputs": result}
        print(f"\nRunning on {args.run}:  {result}")

    if args.certify:
        report = certify_derivation(graph, engine, {name: get_backend(name) for name in args.certify})
        summary["certificate"] = report
        print("\nIndependent check by proof assistants:\n" + render_report(report))
        if args.proofs:
            print(f"(proof files kept in {os.path.abspath(args.proofs)})")

    print("\nDerivation:\n" + export_graph_text(graph))
    if args.json:
        with open(args.json, "w", encoding="utf8") as handle:
            json.dump(summary, handle, indent=2)
    return 0


def spec_frame_names(spec):
    from FormalLLM.refinement.frame import frame_names
    return frame_names(spec.frame)


if __name__ == "__main__":
    sys.exit(main())
