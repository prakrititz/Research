# 10 — Progress Log

Newest first. One entry per working session, so you can see what changed and why.

## 2026-10-04 (evening) — The other problems measured, division fixed, a prover that stops being unlucky, and the pilot's ceiling

**You asked** to carry on with the model-driven runs, and whether I need your credentials. I do not: the model login stays in your user folder, the batch files read it there and never print it, and this workspace cannot reach the model anyway. So the runs are the double-clickable files, and I read the result files they leave.

**1. The first full batch (run on your laptop) is in.** The 11 other solvable benchmark problems, 20 trials each, same settings as the square-root study. Ten succeeded in **every** trial (200 / 200; each case 84-100 % at 95 %), every step proved, Coq re-checked, and all 201 derived programs run correctly against the case's own specification (`cross_check.py`). **Integer division succeeded 1 time in 20**; the other 19 used all 30 calls (3.5 minutes each). The impossible-specification control gave **0 successes in 5** (it gives up after 16 calls), so no soundness alert. Three of the passing cases have specifications a trivial program satisfies (`x = 0`, `i = N`), so their 20 / 20 says less than it looks (`14`, §5e).

**2. Why division failed, and the fix.** Reading the transcripts: the model chose the right loop in its first replies every time. The engine then handed back a set-up (`q := 0; r := n`) and a body (`r := r - d; q := q + 1`), each needing *two* assignments in a row, and the leaf assist only closed one-line goals; the model's middle assertions never worked out. The assist (`FormalLLM/agent/assist.py`) now (a) solves an equation of the postcondition for a variable (`q*d + r = n` gives `r := n - q*d`) and (b) closes a two-variable goal with two assignments in a row, found by a search that stops after 4 seconds. Both only *propose*: the engine and Z3 check every step, and the refiner records the split like a model's, so the Coq certificate covers it (`13`, §8; `tests/test_assist_pairs.py`, 18 tests). The assist's hundreds of small guesses are always checked with Z3, even when a run uses Lean or Coq as its backend, so a run cannot suddenly become a hundred times slower.

**3. Evidence, and its limit.** Replaying all 20 stored division trials through the new code offline (the model's stored replies, no network): **all 20 now finish, in 2 to 6 calls.** Of the 399 earlier stored runs (the 200 of the cases above, v6 and v5), 398 still come out identical; the one that differs (v5 trial 72) already differed before this change. The five stored control trials replay identically too (still five failures). That is evidence, not a measurement; the stored replies answered different prompts. The measurement is `run_v7_check.bat` (20 trials of division, then the 5-trial control).

**4. A discovery about the prover.** Checking the HumanEval practice problems by hand, Z3 "timed out" on the loop of the primality check, and then proved the identical step in milliseconds on another run (5 rejected, 1 proved in 6 repeats; the text sent to Z3 was byte-identical; across 12 random seeds 7 proved it in under 10 ms and 5 timed out). So the prover now tries an obligation in up to four short runs, each rebuilt from scratch with its own seed, and then in one patient run. A proof is a proof whatever the seed, so nothing becomes unsound. `is_prime` and `gcd` now go through in about 2 s every time (`14`, §5f; `tests/test_z3_restarts.py`).

**5. The HumanEval pilot, ready but not run.** `HumanEval/60` (sum 1..n) had only `r` in its frame, so the only program it could express was a closed form no prover here can check; it now has a loop counter and moves to tier B (the specification is still checked against every test input: 12 of 12). New `benchmarks/datasets/he_oracle.py` holds a hand derivation for **eleven of the twelve** problems and runs each through the engine, the emitted Python and the real tests, no model: **eight pass every original and EvalPlus test; three (`gcd`, `is_prime`, `iscube`) are proved correct but too slow** for EvalPlus's huge inputs (10^10 to 10^12) and time out. Correct and fast enough are different properties and only the first is proved. One problem (`has_close_elements`) was not derived by hand. `run_humaneval_pilot.bat` starts the model run (`16`, §5.2: what to expect, and the tier-by-tier order); a run lost to the network is labelled `NETWORK`, not counted, and repeated.

**6. Two small bugs found on the way.** (a) EvalPlus looked "not installed" whenever the whole test suite ran, because several scripts put `benchmarks/` first on the search path and our own `benchmarks/datasets` then shadowed the Hugging Face `datasets` library it needs; the HumanEval pipeline tests were being skipped without a word. Fixed in `benchmarks/datasets/humaneval.py` (`tests/test_evalplus_import.py`). (b) `cross_check.py` had no start value for a loop counter that the precondition pins (`i = 0`), so those programs were wrongly reported as failing or crashed the checker; it now supplies the pinned value and reports a crash instead of dying.

**Tests:** 353 → 399 collected; **380 pass here, 19 are skipped** (Coq and Lean are not installed in the cloud workspace), 0 fail. The 25 skipped in the previous entry included 6 HumanEval pipeline tests skipped by mistake (see 6b above); they run now. New files: `test_assist_pairs.py`, `test_z3_restarts.py`, `test_he_oracle.py`, `test_evalplus_import.py`.

**Not done, and needs you.** (1) Double-click `run_v7_check.bat`: it re-measures division and the control with all of today's code. (2) The refinement pilot with the model (`run_humaneval_pilot.bat`). (3) The strict-rule / no-assist / medium-effort / second-model arms. (4) Sending `18` to Dr. Hou (it needs your name and your decision). Nothing was committed; the working tree still holds many uncommitted edits.

**Files changed or added:** `FormalLLM/agent/assist.py`, `FormalLLM/agent/refiner.py`, `FormalLLM/verification/z3_backend.py`; `benchmarks/cross_check.py`, `benchmarks/datasets/he_refine.py`, `benchmarks/datasets/he_specs.py`, `benchmarks/datasets/humaneval.py`, new `benchmarks/datasets/he_oracle.py`; new `run_v7_check.bat`, `run_humaneval_pilot.bat`; the four test files above plus changes to `test_cross_check.py` and `test_he_refine.py`; notes `00`, `06`, `07`, `13`, `14`, `15`, `16`, `17`. Written by your batch, not by me: `benchmarks/results/reliability/cases_*.jsonl`, `cases_summary.md`, `cases_cross_check.txt`. Running `benchmarks/classic.py` once rewrote `benchmarks/results/classic.json` (same steps and obligations as before; the timings differ slightly).

## 2026-10-04 — The baseline bug, the proved programs actually run, and a one-command batch for the other problems

**You asked** for the next steps toward the paper's outcome: finish the HumanEval baseline, measure the problems other than the square root, and get the questions to Dr. Hou.

**A limit to know about.** This session ran in a cloud workspace linked to your computer. That workspace's network blocks the hosted model's address and does not hold its login, so **no model call was made today**. Everything below is offline work on stored results, plus a batch you run yourself.

**1. The HumanEval baseline scored 0 / 164 because of a bug, not the model.** The hosted endpoint answers in a forced JSON object, so every reply looked like `{"code": "python\n..."}`. The extractor only knew Markdown fences, so it ran the JSON text as Python and every problem failed. `humaneval.extract_code` now opens JSON replies and drops a stray `python` line; new baseline runs ask the endpoint for plain text. Re-scored offline from the stored answers (after checking the harness still accepts 164/164 reference solutions): **156 of 164 on the original tests, 147 of 164 on EvalPlus**, against the paper's GPT-4 alone at 145 / 128 and Refine4LLM at 150 / 150 (`16`, §4). A modern open model alone has caught up with the paper's baseline, which changes what the project can honestly claim: refinement's value is now the proof, not extra passing tests. On the 12-problem pilot the direct model gets 11 right and fails only `HumanEval/24`.

**2. The proved programs also run.** New `benchmarks/cross_check.py` runs every stored derived program on concrete inputs and checks it against the case's own formal specification and the old baseline's hard-coded checker. All 99 successful v6 square-root derivations ended in the same program and pass on the baseline's 12 hard-coded inputs plus 200 random ones (`14`, §5c). The checker is tested against a wrong program and a runaway loop.

**3. One of the "failures" in the latest 100-trial study was the network, not the method.** Trial 3 of v6 never got a reply (`getaddrinfo failed` on all four attempts) but was filed as `EXHAUSTED`. On the trials that reached the model, v6 is **99 of 99**. A trial whose every call failed to connect is now labelled `NETWORK` and left out of the success rate (`FormalLLM/llm/transport.py`; the summariser applies it to old files too). Every earlier failure (v1-v5) was a genuine 30-call search failure.

**4. A batch for the other problems.** `benchmarks/reliability_batch.py` runs the 12 other benchmark cases with the v5/v6 settings, resumes after an interruption, treats `A4-impossible` as a negative control (any success there raises a soundness alert), and ends with a summary table and the cross-check. A one-call model check before each case stops the batch at once if the model cannot be reached, and the slow impossible control runs last. `run_other_cases.bat` in the repository folder starts it with a double-click (it reads the login from your user folder and never prints it). Tested offline with fake results; **not yet run against the model**: this session's network cannot reach the model and its terminal access is click-only, so it needs you to start it.

**5. The notes.** `14` (§5, §5c, §5d) and `16` (§4, §5.2) now hold real numbers instead of placeholders; `17` has the new commands.

**Tests:** 320 → 353 (328 pass here, 25 skipped because Coq and Lean are not installed in the cloud workspace; 0 fail). New files: `test_extract_code.py`, `test_cross_check.py`, `test_reliability_batch.py`, `test_network_outcome.py`.

**Not done.** The 12-case reliability batch; the refinement pilot on the 12 HumanEval specs; the strict-rule / no-assist / medium-effort / second-model arms; sending `18` to Dr. Hou (it needs your name and your decision).

**Files changed or added today:** `benchmarks/datasets/humaneval.py`, `benchmarks/datasets/direct_baseline.py`, `benchmarks/harness.py`, `benchmarks/reliability.py`, `benchmarks/summarize_reliability.py`, `benchmarks/replay.py`, new `benchmarks/cross_check.py`, `benchmarks/reliability_batch.py`, `run_other_cases.bat`, `FormalLLM/llm/transport.py`, the four test files above, `benchmarks/results/datasets/direct_baseline_gpt-oss-120b-low_rescored.jsonl`, and notes `10`, `14`, `16`, `17`, `00`.

## 2026-10-03 (afternoon) — Reading the failed runs, and what that changed

**Why this entry exists.** After the general prompt and the first hardening, the square-root example still failed about 3 runs in 10 (7 of 10 within 30 LLM calls). I did not tune the prompt further. I read the **transcripts of the failed runs** and traced each failure to the step that caused it. They had three causes, and none was the wording of the prompt:

1. **The advice was addressed to the wrong step.** The loop body `x := x + e` was refuted at `x = -3`. The message said "strengthen the invariant" — but the body cannot change the invariant, its *parent* chose it. The model answered with nested loops instead (16 LLM calls gone).
2. **The parent was told about the wrong failure.** When that subtree finally failed, the parent was shown one of *the system's own quick tests* of a different node, and blamed an innocent choice.
3. **The step that owned the call allowance was declared dead** instead of being allowed to repair itself.

**Fixes (all in `13`, §5.1; all with tests in `FormalLLM/tests/test_repair.py`):** each proof obligation now carries advice specific to it; the failure digest follows an accepted-but-failed step down to the part that failed and ignores the system's probes; the allowance belongs to a step, which may try again; and a new **missing-fact diagnosis**: when the obvious body is refuted the system asks the prover "would it be valid if the precondition also guaranteed `x >= 0`?" — and tells the parent to add exactly that to its invariant, with no LLM call spent on the body.

**Then a second round.** With those in, 29 of 30 runs succeeded. I read the one failure too: the model had put the guard's own condition into the invariant, which makes the loop body *impossible* when `N = (x+e)²` — and spent 30 calls below it. Two more general checks, both cheap, both with tests:
* **Every sub-specification a step creates must be *feasible*** (Morgan's notion: from every state satisfying the precondition, some state satisfies the postcondition). An infeasible one cannot be refined by any program, so the step is refused at once with the exact values. The old "set-up step must be possible" check was the special case for one sub-spec.
* **A formula may only use the specification's own names.** The model had written `V = N - (x+e)*(x+e)` and used `V` as a variable; the prover took `V` as an arbitrary constant. Now: "the name V is not defined here; the names are x, N, e".

**Coq certification gap found and fixed.** One run's derivation had a `skip` that Z3 proved but Coq could not: the translator had declared `x` an integer because of `x = 0`, then cast it into real arithmetic. A bare numeral no longer forces an integer sort, and `subst` is a fallback tactic.

**New command line.** `python main.py --case C5-sqrt-paper --config gpt-oss-120b-low --assist --certify coq lean` goes from a specification to a program, then has Coq and Lean re-check it (see `15`).

**Measurements** (all in `14`): old code 7/10; after the diagnosis fix 29/30 (one budget stop, analysed above); the final code is being measured now over 100 + further trials, with the strict termination rule, without the assist, at other reasoning efforts, and with a second model. Raw results are in `benchmarks/results/reliability/`.

**Later the same day — a third round, and the datasets.**
* **A third failure class (F6 in `14`).** In the 100-trial run the first failure was a *legal but useless first move*: splitting on `x*x <= N` where `x` is the answer variable and nothing constrains its starting value. The engine now refuses a split whose test mentions a variable whose entry value is arbitrary, and the call allowance below one step was cut from 16 to 10 (the owner of an exhausted allowance may retry, so 16 + 16 had been eating the whole budget).
* **Efficiency.** Lean: checking all of a derivation's obligations in *one* process (about 10 s, almost all of it loading Mathlib) instead of one process each. A timed-out `coqc` now takes its worker process with it (six orphans had been burning CPU for half an hour: found by looking at the machine, not by a test).
* **Lean and Coq in the search, not only after it.** New backend `z3+lean`: Z3 decides; only if Z3 answers *unknown* is Lean asked to prove the step, and only a proof is accepted (kernel-checked). Lean never overrules a Z3 counterexample.
* **Booleans in Coq/Lean** (needed for the true/false HumanEval problems): a Boolean variable is a proposition.
* **A real bug found while preparing the datasets.** The Python we emitted for a derived program used `/` for every division, but the prover reads `/` on two integers as whole-number division. A *proved* evenness test `n = 2 * (n / 2)` was always true when run. New emitter `FormalLLM/lpl/typed_python.py`, wired into the harness and the old benchmark runner; tests pin the example. (Any earlier benchmark result for a program with integer division was computed with the wrong emitter.)
* **Datasets** (`16`): HumanEval is classified by what the language would need (53 of 164 problems fit); 12 formal specifications written, **checked against the reference solutions on every HumanEval and EvalPlus input and mutation-tested** (the check caught two of my specifications that were wrong because `~` binds weakest in the specification language); the direct-model baseline and the refinement pilot are scripted and tested with a scripted model. The Table-7 analogue now records Coq and Lean certification (`classic.json`: Lean 21 of 21, Coq 9 of 21).
* **New tools for you:** `main.py` (one command, start to finish), `benchmarks/replay.py` (re-derive any stored study offline), `benchmarks/summarize_reliability.py` (one table of many studies), and docs `17` (every command) and `18` (questions for Dr. Hou, ready to forward).
* **Tests:** 230 → 320 (all pass).

## 2026-10-03 — Your three goals, and what stopped

**Your instructions:** (1) reproduce the same *type* of results as the paper; (2) fix the two pure bugs now; (3) build a **general** prompt so the paper's square-root example is solved by refinement **reliably — not "1 out of 20", always** — and *then* add **automated Lean and Coq**, and finally **reproducible results on the datasets**.

**The plan, in the order you set:**

| Phase | Goal | Status |
|---|---|---|
| 1 | General prompt + engine fixes; sqrt solved reliably (measured over many trials) | **in progress** (see below) |
| 2 | Automated Lean 4 and Coq/Rocq proof backends next to Z3 | installs started, **no backend code yet** |
| 3 | Paper datasets (HumanEval/EvalPlus, CorC problems) and reproducible tables | helper code started, **untested** |

**Phase 1 — done so far (all in the working tree, nothing committed):**
* The two bugs you approved: a budget stop is no longer swallowed and mislabelled; reply keys like `I`/`G`/`V` are accepted (and a misspelt key now gives a precise error instead of silently using a default).
* **A third bug found on the way:** a model-written `!(x < 0) && y > 1` was parsed as "not both", i.e. `~((x<0) /\ (y>1))` — the prompt tells models to write `!`, so this silently changed what they meant. Each negation now applies only to its own operand.
* A new readable renderer for specifications (`FormalLLM/llm/spec_render.py`): conjunctions as bullet lists, minimal parentheses, and the loop variant's starting value shown as one named constant `V0` instead of `N0`/`x0`/`e0` copies of constants.
* The hosted model accepts `reasoning_effort`: one call takes about 24 s by default, 12 s at `medium`, 7 s at `low`. It serves **one request at a time**, so running trials in parallel gives no speed-up; the low setting is what makes studies of 20+ trials affordable.

**Phase 1 — still to do:** the new prompts (laws with their *instantiated* proof conditions, a general loop-design recipe, examples from unrelated problems), a structured explanation of a sub-goal's failure for its parent, a cap on chains of `strengthen_post`/`weaken_pre`, a clearer failure message (which part of the goal fails, with the value of `V0`), a reliability runner (N trials, counts and a confidence interval), then the measurements.

**What stopped:** the two background workers I had started for Phase 2 and Phase 3 were terminated by your **account's weekly usage limit** (it resets at 10:30 pm IST). They did not fail on their tasks. Their partial work:
* **Installed on your machine (Phase 2):** *Rocq Platform 2026.07.0 (Rocq 9.1)* in `C:\Users\Prakrititz Borah\.formalllm\rocq` (about 1.9 GB; `bin\coqc.exe` exists), installed for your user only (no admin). The installer copy (515 MB) is still in `C:\Users\Prakrititz Borah\.formalllm\downloads` and can be deleted. **Lean is not installed yet.**
* **Installed on your machine (Phase 3):** Python packages `evalplus` 0.3.1 and `datasets` 4.8.4 (`pip install --user`).
* **Written (Phase 3):** `benchmarks/datasets/humaneval.py`, `benchmarks/datasets/__init__.py`, `benchmarks/datasets/_shim/resource.py` — a HumanEval/EvalPlus test runner, **not yet tested**.
* **Not written:** the Coq/Lean backends, the translators, `15_Coq_and_Lean_Backends.md`, `16_Datasets_and_Reproduction.md`.

**How to undo the installs:** delete the folder `C:\Users\Prakrititz Borah\.formalllm\rocq` (it contains `Uninstall.exe`) and run `pip uninstall evalplus datasets`.

## 2026-10-02 (later) — Paper alignment before any further code changes

**You asked** that we get "on the same page" with your professor's paper before moving forward, that the system be robust, and that I use the hosted LLM to find where sqrt goes wrong.

**What I did (no source code changed in this step):**
* Read the whole paper (36 pp.) and wrote `11_The_Paper_Explained.md` (every number from Tables 6-9 transcribed).
* Compared paper vs code and wrote `12_Paper_vs_Our_Implementation.md` (17 gaps G1-G17, 10 decisions D0-D9).
* Saved the LLM endpoint login **outside the repository**, in a one-line file `.formalllm/remote_auth` in your user profile folder (`user:password`), so Git cannot see it. The working tree contains no copy of it; a text-file scan of all 23 commits also found no match (the password, and its base64 form, appear nowhere in history).
* Started a live `gpt-oss-120b` run on the paper's sqrt case, writing to a temp folder (not the repo's `results.jsonl`).

**Findings:** Z3 is not the bottleneck (0.018 s for the sqrt derivation); our default strict termination rule rejects natural answers the paper accepts (2 of 6 vs 4 of 6 offline) but the existing end-to-end ablation shows the same number of successes in both modes (it only costs more calls); the prompt has problem-specific text (`sqrt`), no syntax rules in the law-choice turn, and thin failure feedback. Details and evidence tags in `12`.

**Main diagnosis from the live run:** the model reproduced the paper's Fig. 2 decomposition by itself, then spent 27 of its 40 calls (the whole budget; 1,668 s; outcome `EXHAUSTED`) in a loop-body subtree that could never succeed (the parent's invariant lacked `x ≥ 0`), because failures below a node are not reported back to it with the counterexample. At the very end it proposed the fully correct loop, but under the keys `I/G/V` instead of `invariant/guard/variant`, and the parser discarded it. The refiner also swallows the budget signal, so the run was mislabelled `EXHAUSTED` instead of `BUDGET` (gaps G16, G17). I also replayed the paper's Fig. 2 *exactly*: our engine rejects its last step in both termination modes (counterexample `x = −3, e = 1, N = 10`); it passes only as partial correctness. See `12` sections 4.0 and 6.

**Waiting on you:** decisions D0-D9 and the question for Dr. Hou (Q1) in `12` section 7.

## 2026-10-02 — Re-orientation + verification hardening

**Context recovery.** I had no memory of earlier sessions, so I re-derived the state from the repo: 4,172 lines of Python, 105 passing tests, 3 GitHub issues (#3 open), recent work on prompt tuning and ablation toggles.

**Key discovery.** The project contains *no Lean or Coq*. The paper (Refine4LLM) uses Coq + CoqHammer; this repo uses Z3 instead. Documented in `08b`.

**Code changes** (uncommitted): Z3 timeout; explicit error for unsupported operators; typed `VerificationUnknown` replaces fragile string matching; fixed an invalid escape sequence; +5 tests (105 → 110, all pass).

**Reading material** created (this folder).

**Open questions for you:** see `08b` §5.

**Not done / caveats**
* Nothing has been run against a live LLM this session, so the effect on benchmark numbers is *unmeasured*. The changes are correctness/robustness fixes, not expected score boosts.
* I did not touch your uncommitted edit in `FormalLLM/llm/prompts.py`.
