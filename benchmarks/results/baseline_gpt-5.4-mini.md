# Baseline: GPT-5.4 mini, no refinement (2026-11-11)

**Setup**
- One prompt per task and one attempt (pass@1). No feedback, retries or refinement.
- The model sees the task's Lean file with the function body left as `sorry`. That file holds the description,
  signature, precondition and postcondition, plus one worked example. The model writes only the body.
- A task counts as passed when the body compiles on our Lean (4.34.1) and passes every test of the task. No proof is
  required.
- Task sets: the tasks whose reference solution compiles and passes every test in our harness
  (`python benchmarks/lean_eval.py reference --dataset D`).
- Settings: temperature 0.4, `reasoning_effort` low.

| dataset | passed every test | compiled |
|---|---|---|
| HumanEval | **122/163** (74.8%) | 127/163 |
| HumanEval, the 159 tasks used for L_spec | **121/159** (76.1%) | — |
| Verina | **119/146** (81.5%) | 121/146 |
| Verina basic | 71/83 | — |
| Verina advanced | 48/63 | — |

**Comparison:** on the same 159 HumanEval tasks, L_spec joint with GPT-5.4 mini reaches **147/159 verified**. Each of
those is a fresh-process Lean proof that the program meets the postcondition, which is stronger than passing tests
(`benchmarks/results/lspec/failures_gpt-5.4-mini_joint.md`).

**Cost:** $0.53 for HumanEval and $0.46 for Verina, plus $0.01 for a 2-task smoke test.

**Files**
- Model replies: `benchmarks/results/{humaneval,verina}/gen_gpt-5.4-mini.jsonl`.
- Scores, with code and errors: `benchmarks/results/{humaneval,verina}/baseline_gpt-5.4-mini.jsonl`.

**Reproduce** (the model calls are paid and need the cap; scoring is local Lean):
```bash
FORMALLLM_MAX_BUDGET_USD=1.5 python benchmarks/lean_baseline.py generate --dataset humaneval --config gpt-5.4-mini --rounds 1
python benchmarks/lean_baseline.py score --dataset humaneval --config gpt-5.4-mini
```
