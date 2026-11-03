"""Run the reliability study on many benchmark cases in one go, then print one table.

The paper's square root (C5) has been measured about 260 times (Reading Material/14). Every other
case has not been measured with the current prompts, so the 99/100 result might be tuned to the
square root. This runs the *other* cases one after another with exactly the settings of the v5/v6
studies (relaxed termination rule, leaf assist on, 30 calls per trial, two-turn protocol), so a
difference between rows is the problem, not the settings.

    export FORMALLLM_REMOTE_AUTH="$(cat "$HOME/.formalllm/remote_auth")"
    export PATH="$HOME/.formalllm/rocq/bin:$PATH"            # so Coq can certify (optional)
    python benchmarks/reliability_batch.py --dry-run          # show what would run, call nothing
    python benchmarks/reliability_batch.py --trials 20        # every case except the square root
    python benchmarks/reliability_batch.py --cases B2-max C4-loop-invariant --trials 10

It can be stopped with Ctrl-C at any time: each trial is saved when it finishes, and running the
same command again only runs the trials that are still missing.

A4-impossible is a *negative control*: its postcondition cannot be satisfied, so refinement must
NOT succeed. It gets fewer trials (every failing trial spends the whole call budget), and any
success on it is reported as a soundness alert, because it would mean the system "proved" an
impossible specification.

At the end it writes ``<prefix>_summary.md`` (success counts with 95 % intervals per case) and
``<prefix>_cross_check.txt`` (the derived programs run on concrete inputs, see cross_check.py).
"""
import argparse
import contextlib
import glob
import io
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "benchmarks")
RESULTS = os.path.join(BENCH, "results", "reliability")
sys.path.insert(0, ROOT)
sys.path.insert(0, BENCH)

from cases import CASES                                        # noqa: E402

#: Already measured about 260 times; left out unless asked for by name.
ALREADY_MEASURED = {"C5-sqrt-paper"}


def existing_trials(prefix: str, case_id: str, results_dir: str = None) -> int:
    """How many trials of this case are already stored under this prefix (so a rerun can resume)."""
    total = 0
    for path in glob.glob(os.path.join(results_dir or RESULTS, f"{prefix}_{case_id}_*.jsonl")):
        with open(path, encoding="utf8") as handle:
            total += sum(1 for line in handle if line.strip())
    return total


def build_command(args, case_id: str, trials: int):
    cmd = [sys.executable, os.path.join(BENCH, "reliability.py"),
           "--config", args.config, "--case", case_id, "--trials", str(trials),
           "--turns", str(args.turns), "--budget", str(args.budget),
           "--max-retries", str(args.max_retries), "--max-depth", str(args.max_depth),
           "--temperature", str(args.temperature), "--timeout", str(args.timeout),
           "--strict", args.strict, "--label", f"{args.prefix}_{case_id}"]
    if args.assist:
        cmd.append("--assist")
    if args.certify:
        cmd += ["--certify", *args.certify]
    return cmd


def plan(args, counts=None):
    """The ordered list of cases with how many trials each still needs."""
    counts = counts if counts is not None else {c["id"]: existing_trials(args.prefix, c["id"]) for c in CASES}
    chosen = args.cases or [c["id"] for c in CASES if c["id"] not in ALREADY_MEASURED]
    by_id = {c["id"]: c for c in CASES}
    unknown = [c for c in chosen if c not in by_id]
    if unknown:
        raise SystemExit(f"unknown case(s) {unknown}; known: {sorted(by_id)}")
    steps = []
    for case_id in chosen:
        case = by_id[case_id]
        control = not case.get("refinable", True)
        want = args.control_trials if control else args.trials
        have = counts.get(case_id, 0)
        todo = max(0, want - have)
        steps.append({"case": case_id, "title": case["title"], "control": control, "want": want,
                      "have": have, "todo": todo, "cmd": build_command(args, case_id, todo)})
    # the negative control runs every trial to its call limit (it cannot succeed), so it goes last:
    # the useful results arrive first
    steps.sort(key=lambda step: step["control"])
    return steps


def parse_args(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cases", nargs="*", default=None,
                    help="case ids to run (default: every case except the square root C5)")
    ap.add_argument("--trials", type=int, default=20, help="trials per solvable case")
    ap.add_argument("--control-trials", type=int, default=5, help="trials for the impossible negative control")
    ap.add_argument("--prefix", default="cases", help="label prefix; result files are <prefix>_<case>_<time>.jsonl")
    ap.add_argument("--config", default="gpt-oss-120b-low")
    ap.add_argument("--turns", type=int, choices=(1, 2), default=2)
    ap.add_argument("--budget", type=int, default=30, help="LLM calls allowed per trial")
    ap.add_argument("--max-retries", type=int, default=4)
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--temperature", type=float, default=0.2)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--strict", choices=("1", "0"), default="0",
                    help="termination rule: 0 = variant must decrease (the paper), 1 = also stay >= 0")
    ap.add_argument("--assist", action=argparse.BooleanOptionalAction, default=True,
                    help="leaf assist (not in the paper); --no-assist turns it off")
    ap.add_argument("--certify", nargs="*", default=["coq"], choices=("coq", "lean"),
                    help="proof assistants that re-check each successful derivation; "
                         "give --certify with nothing after it to switch certification off")
    ap.add_argument("--no-preflight", action="store_true",
                    help="skip the one-call model check that runs before each case")
    ap.add_argument("--dry-run", action="store_true", help="print the commands and stop")
    return ap.parse_args(argv)


def preflight(args):
    """One tiny model call, so an unreachable endpoint stops the batch in seconds instead of wasting hours.

    Returns (reachable, note). Any exception counts as unreachable. An empty reply does not: a
    reasoning model can spend a small token allowance thinking and still be perfectly reachable.
    """
    import run_bench
    started = time.time()
    try:
        provider = run_bench.make_provider(run_bench.CONFIGS[args.config], 0.0, min(args.timeout, 180))
        with contextlib.redirect_stdout(io.StringIO()):            # the provider echoes every prompt
            provider.generate('Reply with exactly this JSON object and nothing else: {"ok": true}', max_tokens=512)
    except Exception as error:
        return False, f"{type(error).__name__}: {error}"
    return True, f"the model answered in {time.time() - started:.0f} s"


def _run_tool(script: str, *tool_args):
    done = subprocess.run([sys.executable, os.path.join(BENCH, script), *tool_args],
                          capture_output=True, text=True, encoding="utf8", errors="replace", cwd=ROOT,
                          env=dict(os.environ, PYTHONIOENCODING="utf8"))
    return (done.stdout or "") + (done.stderr or "")


def finish(args, steps):
    """Write and print the summary table and the cross-check of whatever has been stored."""
    pattern = os.path.join(RESULTS, f"{args.prefix}_*.jsonl")
    files = glob.glob(pattern)
    if not files:
        print("\nno results stored yet, nothing to summarise.")
        return
    table = _run_tool("summarize_reliability.py", pattern, "--markdown")
    summary_path = os.path.join(RESULTS, f"{args.prefix}_summary.md")
    with open(summary_path, "w", encoding="utf8") as handle:
        handle.write(table)
    print("\n==== success per case (95% Wilson intervals) ====\n" + table)
    print(f"(saved to {summary_path})")

    controls = {s["case"] for s in steps if s["control"]}
    for path in files:
        for line in open(path, encoding="utf8"):
            if line.strip():
                rec = json.loads(line)
                if rec["case_id"] in controls and rec["outcome"] == "SUCCESS":
                    print(f"\n!!! SOUNDNESS ALERT: {rec['case_id']} is unsatisfiable but a trial reports SUCCESS "
                          f"({os.path.basename(path)}). Read that trial before trusting any other number.")
    cross = _run_tool("cross_check.py", pattern)
    cross_path = os.path.join(RESULTS, f"{args.prefix}_cross_check.txt")
    with open(cross_path, "w", encoding="utf8") as handle:
        handle.write(cross)
    print("\n==== do the proved programs also run correctly? (tail of cross_check) ====")
    print("\n".join(cross.strip().splitlines()[-16:]))
    print(f"(full output in {cross_path})")


def main(argv=None):
    args = parse_args(argv)
    steps = plan(args)
    print(f"{len(steps)} case(s) planned, prefix '{args.prefix}', model {args.config}, "
          f"assist={'on' if args.assist else 'off'}, strict={args.strict}, "
          f"certify={'+'.join(args.certify) if args.certify else 'off'}")
    for s in steps:
        kind = "negative control" if s["control"] else "solvable"
        print(f"  {s['case']:20s} {kind:16s} want {s['want']:>3d}  stored {s['have']:>3d}  to run {s['todo']:>3d}")
    if args.dry_run:
        for s in steps:
            if s["todo"]:
                print("\n" + " ".join(s["cmd"]))
        return 0

    import run_bench
    if run_bench.CONFIGS[args.config]["kind"] == "openai" and not os.environ.get("FORMALLLM_REMOTE_AUTH"):
        raise SystemExit("FORMALLLM_REMOTE_AUTH is not set. In Git Bash:\n"
                         '  export FORMALLLM_REMOTE_AUTH="$(cat "$HOME/.formalllm/remote_auth")"')
    if "coq" in (args.certify or []) and not shutil.which("coqc"):
        print("WARNING: coqc is not on PATH, so successful derivations cannot be certified. In Git Bash:\n"
              '  export PATH="$HOME/.formalllm/rocq/bin:$PATH"\n'
              "Continuing; certification will be recorded as unavailable.")

    env = dict(os.environ, PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf8")
    failed, unreachable = [], False
    try:
        for i, s in enumerate(steps, 1):
            if not s["todo"]:
                print(f"\n=== {i}/{len(steps)} {s['case']}: already has {s['have']}/{s['want']} trials, skipped ===")
                continue
            if not args.no_preflight:
                reachable, note = preflight(args)
                if not reachable:
                    print(f"\n!!! The model could not be reached ({note}).\n"
                          "    Nothing more was started. Check that the model server and its tunnel are up and that the "
                          "internet works, then run the same command again: finished trials are kept.", flush=True)
                    unreachable = True
                    break
            print(f"\n=== {i}/{len(steps)} {s['case']}: {s['title']} - {s['todo']} trial(s) ===", flush=True)
            code = subprocess.run(s["cmd"], cwd=ROOT, env=env).returncode
            if code != 0:
                print(f"!!! {s['case']} exited with code {code}; going on to the next case", flush=True)
                failed.append(s["case"])
    except KeyboardInterrupt:
        print("\nInterrupted. Finished trials are saved; run the same command again to continue.")
    finish(args, steps)
    if failed:
        print("\ncases whose run stopped with an error:", ", ".join(failed))
    return 1 if (failed or unreachable) else 0


if __name__ == "__main__":
    sys.exit(main())
