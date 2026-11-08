# Working on this repository

Start with [`HANDOFF.md`](HANDOFF.md) (state, setup, what to do next), then
[`Reading Material/29_LSpec_Workflow.md`](Reading%20Material/29_LSpec_Workflow.md).

## Goal

Match or beat Refine4LLM (150/164 HumanEval) with an automated refinement prover. The model never writes proofs: it
chooses laws and writes their parameters in L_spec; Lean proves every obligation.

## Rules

* Commits and pull requests: no `Co-Authored-By` or "Generated with Claude" lines.
* Paid model runs only after the owner approves, always with a hard `--max-usd` cap and `--paid-ok`.
* Never print, log or commit credentials (`~/.formalllm/openai_key`, `~/.formalllm/remote_auth`). Never type a password
  into a command or file yourself: the owner puts it in the credentials file.
* Say what a run will do (and roughly how long) before starting it; keep progress notes short.
* One Lean-heavy job at a time (each REPL holds 4–6 GB). Do not run the whole pytest suite at once; run the files you
  need (`FormalLLM/tests/test_lspec.py`, `test_lean_dynamic.py`, ...).
* Do not re-add a "Placeholder axioms" section to the README.
* Do not work around a denied permission; ask.
* Never send email or messages on the owner's behalf.
* Commit and push finished work to `main` (keep pushing as you go).

## Checking a change

* Translator change: `python benchmarks/lspec_steps.py --dataset <d>` (and `--no-lean` first), `lspec_equiv.py
  --transform lspec`, `lspec_specs.py`, on humaneval, classic and verina; every count must stay full.
* Feedback or repair change: re-check saved replies without a model,
  `python benchmarks/lspec_applier.py --dataset humaneval --model replay:<results.jsonl> --level elaborate`.
* Prover change: `python benchmarks/lspec_run.py --dataset humaneval --model gold ... --attempts 1 --retractions 0`;
  a task counts only if the fresh-process check (`file_check`) says verified.
