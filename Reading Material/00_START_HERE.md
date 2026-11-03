# START HERE

Welcome. This folder is written for you as a newcomer to formal methods. You do **not** need to read the code to follow it. Each file is self-contained but builds on the previous.

## The state of the project in 60 seconds

* LLMs write code that *looks* right. This project makes them write code that is *proved* right: **Refine4LLM** (your professor's paper), reimplemented.
* Method: **refinement calculus**. Start from a specification ("find x with x² ≤ N < (x+e)²"). The LLM repeatedly picks a *law* (e.g. "use a loop") and fills in its parameters (the loop invariant). A prover checks every step. Only checked steps are kept. When every piece is trivial, the pieces assemble into a program.
* **Square root (your first requirement): reliable.** After rebuilding the prompt and, more importantly, *what the model is told after a failure*, the paper's square-root example is solved in 2–5 model calls; the measured success counts are in **`14`**.
* **Beyond the square root (new, 2026-10-04):** the 11 other solvable benchmark problems were run 20 times each. Ten succeeded every time (200 / 200, every step proved, Coq re-checked, and all derived programs run correctly); integer division failed (1 / 20) because the leaf assist could not close a two-assignment goal, which is now fixed and, replayed offline on the stored trials, finishes all 20. The impossible-spec control correctly never succeeded (0 / 5). Details: **`14`**, §5e.
* **Lean and Coq (your second requirement): automatic.** The search uses Z3 (fast, gives counterexamples); every finished derivation is then **re-checked by Coq and by Lean** with one command (`main.py … --certify coq lean`). Lean's `grind` is stronger than Coq's standard tactics on quantified statements (measured in **`15`**).
* **Datasets (your third requirement): a first honest slice.** The test harness for HumanEval/EvalPlus works (164/164 reference solutions pass); formal specifications for a 12-problem pilot are written **and checked against the reference solutions**; the direct-model baseline for all 164 is measured — **156 / 147** programs pass the original / EvalPlus tests, already above the paper's GPT-4 alone (145 / 128) — and the refinement pilot has not been run with the model yet; without a model, hand-written derivations of eleven of the twelve pilot problems are accepted by the engine, eight of them pass every test and three are proved correct but too slow for EvalPlus's huge inputs (**`16`**, §5.2). The paper's own formal specifications are not public — a question for Dr. Hou (**`12`**, Q2).

## Reading order

| # | File | Time | What you get |
|---|---|---|---|
| ★ | `14_Reliability_Study.md` | 30 min | **Does the square root *always* work? How it was measured, what failed, what fixed it** |
| ★ | `16_Datasets_and_Reproduction.md` | 30 min | **HumanEval / EvalPlus: what can and cannot be reproduced, with numbers** |
| ★ | `15_Coq_and_Lean_Backends.md` | 40 min | **What "automated Lean and Coq" means here, what was installed, what was measured** |
| ★ | `17_Cookbook_How_To_Run_Everything.md` | 10 min | **Every command, with what to expect** |
| ★ | `13_The_General_Prompt_and_Hardened_Engine.md` | 40 min | The general prompt (professor's critique) and the engine fixes |
| ★ | `11_The_Paper_Explained.md` | 45 min | Your professor's paper in plain language, with every number from it |
| ★ | `12_Paper_vs_Our_Implementation.md` | 45 min | Where our code differs from the paper; **decisions needed from you; questions for Dr. Hou** |
| 1 | `01_Project_Big_Picture.md` | 30 min | What the project is, one full run end to end |
| 2 | `02_Formal_Methods_Primer.md` | 60 min | What "provably correct" means (specs, Hoare logic, invariants) |
| 3 | `06_Z3_and_SMT_Primer.md` | 45 min | The solver that checks proofs during the search |
| 4 | `08a_Refinement_Calculus_Explained.md` | 60 min | The laws the engine applies |
| 5 | `03_Theorem_Provers_Landscape.md` | 45 min | Z3 vs Coq vs Lean vs Isabelle vs Dafny |
| 6 | `04_Coq_Primer.md` / `05_Lean_Primer.md` | 60 min each | Coq / Lean 4 from zero |
| 7 | `07_Codebase_Tour.md` | 45 min | Map of the code, "where do I change X?" |
| — | `08b_Issues_and_Roadmap.md` | 30 min | The original issue list (partly superseded by `10`–`16`) |
| — | `09_Glossary.md` | reference | Every term, plain English |
| — | `10_Progress_Log.md` | 5 min | What changed, session by session |

## What I need from you

1. **Decision D1** (`12`): which termination rule is the default — the stricter one our code uses, or the paper's relaxed one? It changes which loop variants a model may use.
2. **Whether the "assist" stays optional.** It is not in the paper (it lets the prover close one-line steps and tell the parent which fact is missing). Results are reported with and without it (`14`).
3. **Questions for Dr. Hou** (`12`): Q1 — the paper's Fig. 2 invariant lacks `x ≥ 0`, which our prover rejects; Q2 — can he share the HumanEval formal specifications and the law library?

## How to use this with me
Write questions or confusions in a file `Reading Material/QUESTIONS.md` (or just tell me). I will answer there and improve the unclear docs. Each file ends with a "check yourself" quiz: if you can answer those, you've got it.

## Honesty note
These documents were written by an AI. Code facts were checked against the repo; numbers marked `[ran]` were measured on this machine; where a detail (a version, an install command) may have changed, the files say so. Raw results live in `benchmarks/results/`, and every study can be replayed offline (`17`).
