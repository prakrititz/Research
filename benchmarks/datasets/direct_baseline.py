"""The paper's baseline rows: the model writes each HumanEval function directly.

Table 6 of the paper compares Refine4LLM with GPT-4 *given only the English problem*. This
runs the same protocol with any configured model: for each of the 164 problems the model is
shown the problem's prompt (signature and docstring), asked for a complete function, and the
program is run on the original HumanEval tests ("base") and on EvalPlus' roughly 80x larger
test set ("plus"). A program passes only if it passes every test.

    python -m benchmarks.datasets.direct_baseline --config gpt-oss-120b-low --out results.jsonl
    python -m benchmarks.datasets.direct_baseline --summarize results.jsonl

The run is resumable (finished tasks are skipped), and every row keeps the model's raw reply,
so the evaluation can be repeated offline without the model.
"""
import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

INSTRUCTION = (
    "Complete the following Python function so that it does what its docstring says. "
    "Reply with the complete function, including its signature, in one ```python code block, "
    "and nothing else.\n\n"
)

#: Table 6 of the paper (programs passing all tests, out of 164): GPT-4 alone.
PAPER_GPT4 = {"humaneval": 145, "evalplus": 128}
PAPER_REFINE4LLM = {"humaneval": 150, "evalplus": 150}


def done_ids(path):
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf8") as handle:
        return {json.loads(line)["task_id"] for line in handle if line.strip()}


def run(args):
    from benchmarks import run_bench
    from benchmarks.datasets import humaneval as he

    cfg = run_bench.CONFIGS[args.config]
    provider = run_bench.make_provider(cfg, args.temperature, args.timeout)
    # The hosted endpoint answers in a forced JSON object unless told otherwise. This protocol asks
    # for a program in a Markdown fence, so ask the endpoint for plain text (extract_code still
    # understands a JSON reply, which is how the first 164 stored replies came back).
    if hasattr(provider, "response_format"):
        provider.response_format = None
    finished = done_ids(args.out)
    problems = he.load_problems()
    ids = he.task_ids()[args.start:args.start + args.limit if args.limit else None]
    for task_id in ids:
        if task_id in finished:
            continue
        prompt = INSTRUCTION + problems[task_id]["prompt"]
        started = time.time()
        error, text = None, ""
        try:
            text = provider.generate(prompt, max_tokens=args.max_tokens)
        except Exception as exc:                          # keep going; the row records the failure
            error = f"{type(exc).__name__}: {exc}"
        llm_seconds = time.time() - started
        row = {"task_id": task_id, "config": args.config, "temperature": args.temperature,
               "prompt_chars": len(prompt), "raw_response": text, "error": error,
               "llm_seconds": round(llm_seconds, 1)}
        if text:
            result = he.run_tests(task_id, he.full_source(task_id, text), plus=True)
            row.update(result.as_dict())
        else:
            row.update({"base": "fail", "plus": "fail", "base_ok": False, "plus_ok": False})
        with open(args.out, "a", encoding="utf8") as handle:
            handle.write(json.dumps(row) + "\n")
        print(f"{task_id:14s} base={row['base']:7s} plus={str(row['plus']):7s} "
              f"{llm_seconds:5.1f}s", flush=True)
    summarize(args.out)


def reevaluate(path):
    """Re-run the tests on the stored replies (no model, no network)."""
    from benchmarks.datasets import humaneval as he
    rows = [json.loads(line) for line in open(path, encoding="utf8") if line.strip()]
    for row in rows:
        if row.get("raw_response"):
            row.update(he.run_tests(row["task_id"], he.full_source(row["task_id"], row["raw_response"]),
                                    plus=True).as_dict())
    return rows


def summarize(path, rows=None):
    rows = rows if rows is not None else [json.loads(line) for line in open(path, encoding="utf8") if line.strip()]
    base = sum(1 for r in rows if r.get("base_ok"))
    plus = sum(1 for r in rows if r.get("plus_ok"))
    print(f"\n{len(rows)} problems attempted | HumanEval {base} | EvalPlus {plus}  "
          f"(paper, GPT-4 alone: {PAPER_GPT4['humaneval']} / {PAPER_GPT4['evalplus']}; "
          f"Refine4LLM: {PAPER_REFINE4LLM['humaneval']} / {PAPER_REFINE4LLM['evalplus']})")
    lost = sorted(r["task_id"] for r in rows if r.get("base_ok") and not r.get("plus_ok"))
    failed = sorted(r["task_id"] for r in rows if not r.get("base_ok"))
    print(f"fail the original tests: {len(failed)}  {failed[:12]}{' ...' if len(failed) > 12 else ''}")
    print(f"pass the original tests but not EvalPlus': {len(lost)}  {lost}")
    return {"attempted": len(rows), "humaneval": base, "evalplus": plus, "lost_on_plus": lost}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", default="gpt-oss-120b-low")
    ap.add_argument("--out", default="direct_baseline.jsonl")
    ap.add_argument("--temperature", type=float, default=0.0)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--max-tokens", type=int, default=4096)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--summarize", metavar="FILE", default=None, help="summarise a finished file and exit")
    ap.add_argument("--reevaluate", metavar="FILE", default=None,
                    help="re-run the tests on a file's stored replies (offline) and summarise")
    args = ap.parse_args()
    if args.summarize:
        summarize(args.summarize)
    elif args.reevaluate:
        summarize(args.reevaluate, reevaluate(args.reevaluate))
    else:
        run(args)


if __name__ == "__main__":
    main()
