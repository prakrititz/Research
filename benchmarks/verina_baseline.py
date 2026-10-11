"""Phase 5: the plain-model baseline on Verina's code task, scored on our Lean (4.34.1).

For each task the model is shown the Lean file with the code region left as ``sorry`` (description, signature, precondition,
postcondition, one worked example) and must write the function body. The body is compiled and run on the task's test cases
(``verina_eval.score``). Only tasks whose GROUND TRUTH passes every case in our harness are used, so a failure is the model's,
not the harness's. Several rounds per task follow the per-problem rule.

Two phases, so the model server (Ollama holds about 7 GB of RAM) and Lean with Mathlib (about 3 GB) never run together; the
laptop's low-memory guard killed the first single-process version:

    python benchmarks/verina_baseline.py generate --config ornith --rounds 3      # model only  -> verina/gen_<config>.jsonl
    python benchmarks/verina_baseline.py score    --config ornith                 # Lean only   -> verina/baseline_<config>.jsonl

Both are resumable. ``--limit/--offset`` select tasks.
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
DATASET = os.path.join(os.path.expanduser("~"), ".formalllm", "verina", "datasets", "verina")
OUT = os.path.join(ROOT, "benchmarks", "results", "verina")
SCORE_TIMEOUT = 90.0
DEF = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:partial|private|noncomputable|protected)[ \t]+)*def[ \t]+(\w+)")


def scoreable_tasks():
    rows = [json.loads(l) for l in open(os.path.join(OUT, "oracle_scores.jsonl"), encoding="utf8")]
    return [r["task"] for r in rows if r["compiles"] and r["tests"] and r["passed"] == r["tests"]]


def function_name(task: str) -> str:
    return json.load(open(os.path.join(DATASET, task, "task.json"), encoding="utf8"))["signature"]["name"]


def prompt_for(task: str) -> str:
    from benchmarks import verina_eval as V
    d = os.path.join(DATASET, task)
    lean = open(os.path.join(d, "task.lean"), encoding="utf8").read()
    skeleton = V.candidate(lean, "  sorry")
    description = open(os.path.join(d, "description.txt"), encoding="utf8").read().strip()
    return ("You are writing a Lean 4 function (Mathlib is imported).\n\n"
            "EXAMPLE of a good answer. For a task whose file had `sorry` as the body of\n"
            "`def countEven (a : Array Int) (h_precond : countEven_precond (a)) : Nat :=`, the complete reply is only:\n"
            "a.foldl (fun acc x => if x % 2 == 0 then acc + 1 else acc) 0\n\n"
            f"TASK DESCRIPTION\n{description}\n\n"
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
    tasks = scoreable_tasks()[args.offset:]
    tasks = tasks[:args.limit] if args.limit else tasks
    path = os.path.join(OUT, f"gen_{args.config}.jsonl")
    done = {(r["task"], r["round"]) for r in jsonl(path)}
    cfg = run_bench.CONFIGS[args.config]
    print(f"generate: {len(tasks)} tasks x {args.rounds} rounds, config {args.config}", flush=True)
    for task in tasks:
        for rnd in range(args.rounds):
            if (task, rnd) in done:
                continue
            provider = provider_for(cfg, args.temperature, args.timeout)
            started = time.time()
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    reply, error = provider.generate(prompt_for(task)), ""
            except Exception as exc:
                reply, error = "", str(exc)[:120]
            row = {"task": task, "round": rnd, "config": args.config, "reply": reply, "gen_error": error,
                   "gen_seconds": round(time.time() - started, 1)}
            with open(path, "a", encoding="utf8") as handle:
                handle.write(json.dumps(row) + "\n")
            print(f"{task:22s} r{rnd} {row['gen_seconds']:5.0f}s {len(reply):5d} chars {error}", flush=True)


def score(args):
    from benchmarks import verina_eval as V
    from benchmarks.lean_persistent import PersistentLean
    gens = jsonl(os.path.join(OUT, f"gen_{args.config}.jsonl"))
    path = os.path.join(OUT, f"baseline_{args.config}.jsonl")
    done = {(r["task"], r["round"]) for r in jsonl(path)}
    todo = [g for g in gens if (g["task"], g["round"]) not in done]
    lean = PersistentLean(imports="import Mathlib", timeout_s=900)
    print(f"score: {len(todo)} attempts (Lean ready in {lean.startup_seconds:.0f} s)", flush=True)
    for g in todo:
        body, aux = split_reply(g["reply"], function_name(g["task"]))
        box = {}

        def work():
            try:
                box["r"] = V.score(lean, g["task"], code=body, aux=aux)
            except Exception as exc:
                box["e"] = str(exc)
        thread = threading.Thread(target=work, daemon=True)
        thread.start()
        thread.join(SCORE_TIMEOUT)
        if thread.is_alive() or "e" in box:                      # a runaway #eval: kill and restart Lean
            lean.process.kill()
            lean.close()
            lean = PersistentLean(imports="import Mathlib", timeout_s=900)
            result = {"compiles": False, "errors": ["timeout or crash while scoring"], "tests": 0, "passed": 0}
        else:
            result = box["r"]
        row = {"task": g["task"], "round": g["round"], "config": args.config, "compiles": result["compiles"],
               "tests": result["tests"], "passed": result["passed"], "errors": result.get("errors", [])[:2],
               "gen_seconds": g["gen_seconds"], "code": body[:1500], "aux": aux[:800]}
        with open(path, "a", encoding="utf8") as handle:
            handle.write(json.dumps(row) + "\n")
        ok = result["compiles"] and result["tests"] and result["passed"] == result["tests"]
        print(f"{g['task']:22s} r{g['round']} compiles={result['compiles']!s:5s} {result['passed']}/{result['tests']} "
              f"{'SOLVED' if ok else '-'}", flush=True)
    lean.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("phase", choices=("generate", "score"))
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
