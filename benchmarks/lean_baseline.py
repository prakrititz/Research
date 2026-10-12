"""The plain-model (direct) baseline on any dataset's code task, scored on our Lean (4.34.1).

For each task the model is shown the Lean file with the code region left as ``sorry`` (description, signature, precondition,
postcondition, one worked example) and must write the function body. The body is compiled and run on the task's test cases
(``FormalLLM.lean.evaluate.score_code``). Only tasks whose REFERENCE solution passes every case in our harness are used
(``python benchmarks/lean_eval.py reference --dataset D`` writes that list), so a failure is the model's, not the harness's.
Several rounds per task follow the per-problem rule. The dataset is a switch; nothing else differs:

    python benchmarks/lean_baseline.py generate --dataset verina    --config ornith --rounds 3   # model only
    python benchmarks/lean_baseline.py score    --dataset verina    --config ornith              # Lean only
    python benchmarks/lean_baseline.py generate --dataset humaneval --config ornith --rounds 3

Two phases, so the model server (Ollama holds about 7 GB of RAM) and Lean with Mathlib (about 3 GB) never run together.
Both are resumable. ``--limit/--offset`` select tasks. Outputs: results/<dataset>/gen_<config>.jsonl, baseline_<config>.jsonl.
"""
import argparse
import contextlib
import io
import json
import os
import re
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from FormalLLM.lean import dataset as datasets
SCORE_TIMEOUT = 90.0
DEF = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:partial|private|noncomputable|protected)[ \t]+)*def[ \t]+(\w+)")


def scoreable_tasks(ds):
    """Tasks whose reference solution compiles and passes every test (from ``lean_eval.py reference``)."""
    path = ds.result_path("reference_scores.jsonl")
    if not os.path.exists(path):                              # Verina's older file name
        path = ds.result_path("oracle_scores.jsonl")
    if not os.path.exists(path):
        raise SystemExit(f"run first: python benchmarks/lean_eval.py reference --dataset {ds.name}")
    rows = [json.loads(l) for l in open(path, encoding="utf8") if l.strip()]
    return [r["task"] for r in rows if r["compiles"] and r["tests"] and r["passed"] == r["tests"]]


def prompt_for(ds, task_id: str) -> str:
    from FormalLLM.lean.evaluate import candidate_source, task_source
    task = ds.load(task_id)
    skeleton = candidate_source(task_source(task), "  sorry")
    return ("You are writing a Lean 4 function (Mathlib is imported).\n\n"
            "EXAMPLE of a good answer. For a task whose file had `sorry` as the body of\n"
            "`def countEven (a : Array Int) (h_precond : countEven_precond (a)) : Nat :=`, the complete reply is only:\n"
            "a.foldl (fun acc x => if x % 2 == 0 then acc + 1 else acc) 0\n\n"
            f"TASK DESCRIPTION\n{task.description}\n\n"
            "LEAN FILE. The function body is `sorry`; the precondition and the postcondition are fixed.\n"
            f"```lean\n{skeleton}\n```\n\n"
            "Replace ONLY the `sorry` in the function body by a correct implementation that satisfies the postcondition. "
            "Reply with the Lean code of the body and nothing else (no explanation, no markdown fences, no theorem).")


def _json_text(text: str) -> str:
    try:
        data = json.loads(text)
    except Exception:
        return text
    stack = [data]
    while stack:
        node = stack.pop()
        if isinstance(node, dict):
            for key in ("code", "body", "lean", "answer", "implementation"):
                if isinstance(node.get(key), str):
                    return node[key]
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return text


def split_reply(reply: str, name: str):
    """``(body, aux)``: the function body, and any helper definitions written before the main ``def``."""
    text = _json_text((reply or "").strip())
    fence = re.search(r"```(?:lean4?|lean)?\s*\n(.*?)```", text, re.S)
    if fence:
        text = fence.group(1)
    aux = ""
    mains = [m for m in DEF.finditer(text) if m.group(1) == name]
    if mains:                                    # the model wrote the whole function: keep the body after its ':='
        main = mains[0]
        aux = text[:main.start()].strip("\n")
        rest, depth, cut = text[main.end():], 0, None
        for i, ch in enumerate(rest):
            depth += ch in "([{"
            depth -= ch in ")]}"
            if depth == 0 and rest.startswith(":=", i):
                cut = i + 2
                break
        text = rest[cut:] if cut is not None else rest
    return text.strip("\n"), aux


def provider_for(cfg, temperature, timeout):
    """The configured model asked for free text (the refinement provider forces a JSON object, which makes small models
    invent their own JSON schema instead of writing code)."""
    if cfg["kind"] != "ollama":
        from benchmarks import run_bench
        return run_bench.make_provider(cfg, temperature, timeout)
    from FormalLLM.llm.provider import OllamaProvider
    return OllamaProvider(model_name=cfg["model"], think=cfg["think"], response_format=None, timeout=timeout,
                          options={"temperature": temperature, "num_predict": 2048, "num_ctx": 8192})


def jsonl(path):
    return [json.loads(l) for l in open(path, encoding="utf8") if l.strip()] if os.path.exists(path) else []


def generate(args):
    from benchmarks import run_bench
    ds = datasets.get(args.dataset)
    tasks = scoreable_tasks(ds)[args.offset:]
    tasks = tasks[:args.limit] if args.limit else tasks
    path = ds.result_path(f"gen_{args.config}.jsonl")
    done = {(r["task"], r["round"]) for r in jsonl(path)}
    cfg = run_bench.CONFIGS[args.config]
    print(f"generate {ds.name}: {len(tasks)} tasks x {args.rounds} rounds, config {args.config}", flush=True)
    for task in tasks:
        for rnd in range(args.rounds):
            if (task, rnd) in done:
                continue
            provider = provider_for(cfg, args.temperature, args.timeout)
            started = time.time()
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    reply, error = provider.generate(prompt_for(ds, task)), ""
            except Exception as exc:
                reply, error = "", str(exc)[:120]
            row = {"task": task, "round": rnd, "config": args.config, "reply": reply, "gen_error": error,
                   "gen_seconds": round(time.time() - started, 1)}
            with open(path, "a", encoding="utf8") as handle:
                handle.write(json.dumps(row) + "\n")
            print(f"{task:30s} r{rnd} {row['gen_seconds']:5.0f}s {len(reply):5d} chars {error}", flush=True)


def score(args):
    from FormalLLM.lean.evaluate import score_code, solved
    from FormalLLM.lean.session import LeanSession
    ds = datasets.get(args.dataset)
    gens = jsonl(ds.result_path(f"gen_{args.config}.jsonl"))
    path = ds.result_path(f"baseline_{args.config}.jsonl")
    done = {(r["task"], r["round"]) for r in jsonl(path)}
    todo = [g for g in gens if (g["task"], g["round"]) not in done]
    with LeanSession(imports="import Mathlib", startup_timeout=1800, command_timeout=SCORE_TIMEOUT) as lean:
        print(f"score {ds.name}: {len(todo)} attempts (Lean ready in {lean.startup_seconds:.0f} s)", flush=True)
        for g in todo:
            task = ds.load(g["task"])
            body, aux = split_reply(g["reply"], task.name)
            try:
                result = score_code(lean, task, body, aux, load_timeout=SCORE_TIMEOUT * 2, test_timeout=SCORE_TIMEOUT)
            except Exception as exc:                       # the session restarts itself on a timeout; anything else is recorded
                result = {"compiles": False, "errors": [f"harness error: {str(exc)[:150]}"], "tests": 0, "passed": 0, "unproved": 0}
            row = {"task": g["task"], "round": g["round"], "config": args.config, "compiles": result["compiles"],
                   "tests": result["tests"], "passed": result["passed"], "errors": result.get("errors", [])[:2],
                   "gen_seconds": g["gen_seconds"], "code": body[:1500], "aux": aux[:800]}
            with open(path, "a", encoding="utf8") as handle:
                handle.write(json.dumps(row) + "\n")
            print(f"{g['task']:30s} r{g['round']} compiles={result['compiles']!s:5s} {result['passed']}/{result['tests']} "
                  f"{'SOLVED' if solved(result) else '-'}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phase", choices=("generate", "score"))
    ap.add_argument("--dataset", default="verina", choices=datasets.names())
    ap.add_argument("--config", default="ornith")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--temperature", type=float, default=0.4)
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()
    (generate if args.phase == "generate" else score)(args)


if __name__ == "__main__":
    main()
