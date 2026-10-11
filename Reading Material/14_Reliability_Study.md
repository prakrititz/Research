# 14 — The Reliability Study: does the square root *always* work?

> **Your requirement:** "not 1 out of every 20 trials — we need *always* yes the model can solve it with refinement." This file is how that requirement was measured, what failed on the way, what fixed it, and what the final numbers do and do not prove.
>
> **Evidence tags:** `[ran]` measured on this machine · `[read]` read in code · `[test]` a unit test enforces it.
> Read `11`–`13` first. All raw results are in `benchmarks/results/reliability/`; every trial keeps the model's raw replies, so each can be replayed offline (`benchmarks/replay.py`).

---

## 1. Why one run proves nothing

A language model is random: ask the same question twice and the answers differ. "It worked when I tried it" says nothing about the 20th try. So the question "does it always work?" has to be turned into *counting*:

> Run the **same** task N times from scratch. Count the successes. Report the count **and an interval**, because a small N leaves a lot of doubt.

The interval used here is the **Wilson 95 % interval**. What it means for "always": if all N trials succeed, you can only claim the failure rate is *probably below* a bound that shrinks slowly with N.

| trials, all succeeded | you can claim, with 95 % confidence, that the success rate is at least |
|---|---|
| 10 | 72 % |
| 30 | 89 % |
| 100 | 96.3 % |
| 300 | 98.7 % |

There is no number of trials after which "always" is *proved*; there are only numbers after which a failure rate above some bound becomes implausible. That is why this study reports counts and intervals rather than "100 %".

---

## 2. The protocol `[read]`

* **Task:** the paper's motivating example (case `C5-sqrt-paper`): given `N ≥ 0` and `e > 0`, find `x` with `x² ≤ N < (x+e)²`.
* **Model:** `gpt-oss:120b`, hosted, `reasoning_effort = low` (about 7–14 s per call). Temperature 0.2. One trial = a fresh run; nothing is carried between trials.
* **Pipeline:** the paper's Algorithm 1: for each specification the model first chooses a *law*, then supplies its *parameters*; the prover checks; failures go back to the model with a counterexample; a node that keeps failing returns to its parent.
* **Limits per trial:** 30 LLM calls in total, 4 attempts per node, depth 6, at most 10 calls under any one non-root step before it is cut off (the step's owner may then try again).
* **Success** = the derivation is complete (every step proved) **and** (when `--certify coq`) Coq re-checks all obligations. **BUDGET** = the 30 calls ran out. **EXHAUSTED** = the root ran out of options. **NETWORK** = every call failed to connect, so the model was never consulted; such a trial is shown but left out of the rate (§5).
* **Arms** (what is varied): the termination rule (`relaxed` = the paper's Lemma 6.7, `strict` = also require V ≥ 0); the *assist* (on/off — not in the paper); the model's reasoning effort; the model.

---

## 3. What happened, version by version `[ran]`

Each row is the **same task and model**; only the code changed. Small-n rows are noisy (n = 10 has a 95 % interval from 60 % to 98 % even at 9/10), so compare the shape, not the decimals.

| Code version | What it contained | Result (relaxed rule, assist on) | Typical successful run |
|---|---|---|---|
| **v1** | general prompt, bug fixes | 9 / 10 | 2 calls |
| **v3** | + credit assignment (parent told why a child failed), subtree cap | 7 / 10 (3 budget stops; 4 of the 7 successes needed 19–22 calls) | 2 calls, or 19–22 |
| **v4** | + per-obligation advice, accurate failure digest, owner retries, *missing-fact diagnosis* | **29 / 30** (1 budget stop) | 2–5 calls |
| **v5** | + every sub-specification must be feasible; invented names refused | **99 / 100** (95 % interval 95–100 %; the one failure is F6 below) | median 2 calls, 13 s; maximum 11 calls |
| **v6** | + a split on a variable whose starting value is arbitrary is refused; call allowance below a step 16 → 10 | **99 / 99** trials that reached the model (the 100th died on a network error, §5) | median 2 calls, 12 s; maximum 9 calls |
| **v8** (2026-10-05) | + the two-assignment search, faithful formula display, typed and executable steps, provers aligned (`10`, newest entry) | **100 / 100** (two sets of 50 with the same code) | median 2 calls; maximum 4 calls |

The point of the table is **not** the move from 7/10 to 29/30. It is that between v3 and v4 the change was *not* to the prompt. It was to what the model is told **after a failure**, found by reading the failed transcripts.

---

## 4. Anatomy of the failures (read from the transcripts) `[ran]`

Every failed or slow trial had the same shape. The model proposes the loop of the paper's Fig. 2, with the invariant `x*x <= N`. That invariant does **not** say `x ≥ 0`. Then the loop body `x := x + e` cannot be proved — it fails for a negative `x` such as −3 — and the search goes wrong in one of several ways:

| # | What went wrong | What the model was told | Fix | Test |
|---|---|---|---|---|
| F1 | The body node saw "strengthen the invariant" but **cannot change the invariant** (its parent chose it). It started nested loops: 16 LLM calls wasted. | advice written for the wrong step | each proof obligation carries advice for *its own* step; the body returns to its parent at once, with the missing fact named (`x >= 0`) | `test_repair.py` |
| F2 | When that subtree failed, the parent was shown one of the **system's own quick tests of another node**, and blamed an innocent choice (changed a correct intermediate assertion to `true`). | misleading evidence | the digest ignores the system's probes, follows an accepted-but-failed step down to the part that failed, and says which of the parent's parameters to change | `test_repair.py` |
| F3 | The step that owned the call allowance was declared dead instead of being allowed to repair itself. | – | the allowance belongs to a *step*; it may propose again | `test_repair.py` |
| F4 | The model put the guard's own condition into the invariant (`... && N >= (x+e)*(x+e)`), which makes the loop body **impossible** when `N = (x+e)²`; it spent all 30 calls below it. | nothing said the body was impossible | every sub-specification a step creates must be **feasible** (some state satisfies its postcondition); refused at once with the exact values | `test_robustness.py` |
| F5 | The model named a quantity (`V = N - (x+e)*(x+e)`) and used `V` as a variable. The prover treated `V` as an arbitrary constant and judged something the model did not mean. | the rejection never said `V` was the mistake | formulas may only use the specification's own names; otherwise "the name V is not defined here; the names are x, N, e" | `test_repair.py` |
| F6 | The first move was `if x*x <= N then … else …` at the root. `x` is the answer variable; nothing constrains its starting value, so the split is on garbage. The else-branch ("x starts too big") needed a different program and ~20 calls went into it. | the split was legal, so nothing objected | a split on a variable whose starting value is arbitrary (the precondition does not mention it, the postcondition does not use its earlier value) is refused with that explanation; the call allowance below one step was also cut from 16 to 10 | `test_repair.py` |

None of these is specific to the square root. F1–F3 are about *who is told what*; F4–F5 are checks that any refinement step should pass.

---

## 5. Results of the final code (v6) `[ran]`

Same task, model and settings as §2 (relaxed termination rule, leaf assist on, Coq certification on), 100 trials per code version:

| Code | Trials | Reached the model | Succeeded | 95 % interval | Calls: median (max) | Wall time, median | Coq-certified |
|---|---|---|---|---|---|---|---|
| v5 | 100 | 100 | 99 | 95-100 % | 2 (11) | 13 s | 99 / 99 |
| **v6** | 100 | **99** | **99** | **96-100 %** | 2 (9) | 12 s | 99 / 99 |
| **v8** | 100 | **100** | **100** | **96-100 %** | 2 (4) | 21 s (two studies shared the model) | 100 / 100 |

**The one miss in each run was a different kind of thing.** v5's was a real search failure: all 30 calls used, analysed in §4 (F6). v6's was **not a search failure at all**: trial 3 never got a single reply. All four attempts ended in `getaddrinfo failed` (the laptop could not look up the model server's address, a network blip), and the code filed it under `EXHAUSTED`, i.e. as if the *method* had failed. On the trials that actually reached the model, v6 succeeded **99 of 99**; with 95 % confidence the success rate is at least 96.3 %.

**A measurement fix that came out of this.** Counting a lost trial as a failure lowers a success rate for a reason that has nothing to do with refinement. Now a trial whose calls *all* failed to connect is labelled `NETWORK` (`FormalLLM/llm/transport.py`, used by `benchmarks/harness.py`), is shown in the summary tables but left out of the rate, and is skipped by `replay.py`. The summariser applies the same rule to the older stored files, which is how v6 reads 99/99 above without rewriting any result. One real reply anywhere in a trial keeps it a genuine trial (`tests/test_network_outcome.py`).

**Do not over-read "99 vs 99".** v5 had one genuine failure in 100 trials, v6 none in 99. That is a difference of one trial: consistent with the v6 changes helping, and with them doing nothing. Only a much larger run, or a harder problem, could tell them apart.

### 5c. Do the proved programs also run correctly? `[ran]`

You asked whether the *tests* and the *proofs* agree. `benchmarks/cross_check.py` takes every successful derivation in a result file, runs the emitted Python on concrete inputs, and asks two independent questions of each output: does it satisfy the case's own formal specification (evaluated with no tolerance), and does it pass the hard-coded check the older direct-code baseline used (`benchmarks/baseline_cases.py`, which has a 1e-9 tolerance)?

* All **99** successful v6 derivations ended in the *same* program (four spellings of the paper's loop: `x = 0; while N >= (x+e)*(x+e): x = x + e`).
* On the baseline's **12 hard-coded square-root inputs** (chosen to hit the three failure modes the paper reports for Copilot, GPT-4 and o1-preview) plus **200 random inputs**, all 99 pass both checks, and none runs forever.
* The checker can fail: `tests/test_cross_check.py` feeds it a program that never moves and a loop that never stops, and both are caught.

What this does *not* show: the proofs are about exact real numbers, and the cross-check runs ordinary Python floats on 212 inputs. Passing is reassuring, not a second proof. And 99 derivations of one program is one program checked, not 99.

```bash
python benchmarks/cross_check.py "benchmarks/results/reliability/v6_relaxed_assist_*.jsonl" --random 200
```

### 5d. The other arms, with the final code

§2 lists four things that can be varied. With the final code (v6) the first three lines of this table have been run (the strict-rule and assist-off rows by the runs of 2026-10-04, evening); the others are still open:

| Arm | Measured with the final code? |
|---|---|
| relaxed rule, assist on, `reasoning_effort = low` (the table above) | yes, 2 x 100 trials |
| strict termination rule | **yes (2026-10-04, v6 code + the evening's assist): 46 of 48 trials that reached the model (96 %, 95 % interval 86–99 %), median 3 calls and 21 s, all 46 Coq-certified.** Against the relaxed rule's 99 / 99 the difference in success is not significant (Fisher p = 0.11); the cost is time. In 23 of the 47 trials with a proposal the model's first variant was `N - (x+e)*(x+e)`, which the strict rule refuses (it goes negative on the last iteration); those trials needed a median of 3 calls, the 24 that started with `N - x*x` a median of 2. **But the relaxed rule has a gap (found on 2026-10-05):** over the integers a measure that only has to decrease can decrease for ever, and one HumanEval `gcd` derivation was accepted with a loop that never stops (measure `a - g`, `g` growing past `a`). Every success reported in these notes has a bounded measure (checked with Z3), so no number changes; the v9 copy repairs the rule by also requiring the measure to be non-negative while the loop runs, which still accepts `N - (x+e)*(x+e)` (`10`, newest entry; `19`, §7). File: `v6_strict_assist_20261004-222127.jsonl` |
| assist off | **yes (2026-10-04, v6 code): 8 of 30 (27 %, 95 % interval 14–44 %)**, against 99 / 99 with the assist (Fisher p ≈ 2 × 10⁻¹⁸). The 8 successes needed a median of 19.5 calls, the other 22 trials used all 30. Reading them: the model proposes the right loop at the root and then answers the trivial set-up (`x := 0`) and body (`x := x + e`) with *more loops* — a loop law was proposed a median of 12 times in a failed trial and 9 times in a successful one, where one is enough. The assist is therefore the largest single factor in the reliability of this model; it does for the trivial steps what instruction tuning did for the paper's GPT-4 (paper, Table 9). File: `v6_relaxed_noassist_20261004-231321.jsonl` |
| medium reasoning effort | **yes (v8 code): 20 of 20** (84–100 %), median 2 calls, 32 s per trial. File `v8_sqrt_medium_20261005-062414.jsonl` |
| a second model (`qwen3-coder-next`) | no |
| **any problem other than the square root** | **yes**: the 11 other solvable cases, 20 trials each (§5e). With the v8 code **all 11 at 20 of 20 (220 / 220)**, every derivation Coq-certified, integer division included; the impossible control 0 of 5. Files `v8cases_*` (summary `v8cases_summary.md`) |

### 5e. The other benchmark problems `[ran]`

§5 measured one problem, the paper's square root, about 260 times. The worry was that the fixes in §4 had been tuned to it. So the other benchmark cases (`benchmarks/cases.py`) were run on your laptop with exactly the same settings: relaxed termination rule, leaf assist on, 30 calls per trial, two-turn protocol, Coq certification, `gpt-oss:120b` at low effort, 20 trials each (`benchmarks/reliability_batch.py`; the files are `benchmarks/results/reliability/cases_*.jsonl`).

| Case | The problem | Succeeded | 95 % interval | Calls: median (max) | Wall time, median | Coq-certified |
|---|---|---|---|---|---|---|
| A1-skip | the precondition already implies the postcondition | 20 / 20 | 84-100 % | 2 (2) | 4 s | 20 / 20 |
| A2-assign | one assignment, `x = N + 1` | 20 / 20 | 84-100 % | 2 (2) | 6 s | 20 / 20 |
| A3-assign-guarded | one assignment that needs the precondition | 20 / 20 | 84-100 % | 2 (2) | 6 s | 20 / 20 |
| B1-sequential | two outputs, `s = A + B` and `d = A - B` | 20 / 20 | 84-100 % | 2 (2) | 6 s | 20 / 20 |
| B2-max | the larger of two numbers (an `if`) | 20 / 20 | 84-100 % | 2 (4) | 7 s | 20 / 20 |
| B3-abs | absolute value (an `if` with a negation) | 20 / 20 | 84-100 % | 4 (4) | 15 s | 20 / 20 |
| C1-sqrt-loose | square root, loose bound `x*x <= N` | 20 / 20 | 84-100 % | 2 (3) | 7 s | 20 / 20 |
| C2-sqrt-tight | square root, tight bound (nonlinear) | 20 / 20 | 84-100 % | 2 (8) | 10 s | 20 / 20 |
| C3-loop-pinned | counting loop whose start value is fixed by the precondition | 20 / 20 | 84-100 % | 2 (6) | 11 s | 20 / 20 |
| C4-loop-invariant | counting loop with a usable invariant | 20 / 20 | 84-100 % | 2 (2) | 7 s | 20 / 20 |
| **D1-intdiv** | **quotient and remainder (two variables, a loop)** | **1 / 20** | **1-24 %** | 26 (26) | 183 s | 1 / 1 |

How to read it.

* **Ten of eleven cases succeeded in every trial** (200 of 200), each with a 95 % lower bound of 84 %. Two model calls were the norm; the worst trial, in C2, took 8. The code is the one whose fixes were found by reading square-root failures (§4); these cases had not been run with the current prompts before and pass without further changes, which argues against the worry that the 99 / 100 was an accident of that one problem.
* **A pass here means the whole chain held:** every step proved by Z3, the finished derivation re-checked by Coq (20 of 20 in each case), and the emitted program is right when run. `benchmarks/cross_check.py` ran all 201 derived programs on the baseline's hard-coded inputs and on random ones against the case's own formal specification: **all pass**, none runs forever. (Several cases end in the same one or two programs; the check counts derivations, not distinct programs.)
* **Three of these cases are weaker than they look.** C1's postcondition `x*x <= N` is satisfied by `x = 0`; C3's and C4's by `i = N`. Several derivations therefore end in `x = 0` or `i = N` (a few keep a pointless `while` around it). Their 20 / 20 shows that the pipeline runs and the proofs check; it does not show that the model finds a clever loop. The loop evidence is C2 (a tight bound, nonlinear) and the paper's own square root (§5).
* **Integer division was the only failure: 1 trial in 20.** Each of the other 19 used all 30 calls (about 3.5 minutes per trial, `BUDGET`). The one that finished did so by a different route (26 calls, a one-variable loop `q` followed by `r := n - q*d`).

**Why division failed (read from the stored transcripts).** The model proposed the right loop in its first replies in every trial: invariant `q*d + r = n && r >= 0`, guard `r >= d`, variant `r`. The engine accepted it and handed back two child problems, the set-up (`q := 0; r := n`) and the body (`r := r - d; q := q + 1`). Each needs **two assignments in a row**, so each needs a `sequential` step whose middle assertion has to be chosen first. The leaf assist could only close a goal with *one* assignment, and the model's middle assertions were wrong or too weak (for example `q*d <= n && q >= 0`, which leaves the second half unprovable), until the sub-tree allowance of 10 calls and then the 30-call budget ran out. The model was never the problem; the leftover bookkeeping was.

**The fix (code version v7).** The assist (`FormalLLM/agent/assist.py`) gained two abilities, both only *proposals* that the engine and Z3 check like any other step (`13`, §8):

1. *Solve an equation for a variable.* From a postcondition conjunct such as `q*d + r = n` it proposes `r := n - q*d`.
2. *Two assignments in a row.* For a goal with two or more frame variables it looks for a middle assertion and two single assignments that Z3 accepts, within a 4-second limit. It found `r := n; q := 0` for the set-up and `r := r - d; q := q + 1` for the body.

The refiner records an assist-made split exactly as it records a model's, so the Coq certificate covers it (`tests/test_assist_pairs.py`, 18 tests).

**Evidence so far, and its limit.** Replaying the 20 stored division trials offline through the new code (the model's own stored replies, no network): **all 20 now finish, in 2 to 6 calls** (`benchmarks/replay.py`). All earlier replays still come out identical (398 of 399; the one that differs, v5 trial 72, differs the same way under the code before this change). This is evidence, not a measurement: the stored replies were given in answer to different prompts than the new code would send. The measurement is the re-run, `run_v7_check.bat` (20 trials of division, then the control below). The fix was found by reading division's failures, so a success there shows the fix works; it is not an independent test of generality. That is what the HumanEval pilot (`16`) is for.

**The control (`A4-impossible`).** Its postcondition (`y = A /\ y < 0` with `A > 0`) cannot be satisfied, so refinement must **never** succeed; any success would mean the system "proved" an impossible specification. Measured with the code **before** the division fix: **0 of 5** trials succeeded (all five ended `EXHAUSTED`, 16 calls and about 2 minutes each), so no soundness alert. The new assist can only propose steps that Z3 then checks, and on the impossible specification it proposes nothing (`tests/test_assist_pairs.py` asserts that nothing unproved is ever returned), and replaying the five stored control trials through the new code gives the same five failures (16 calls each, `benchmarks/replay.py`); but the control has to be run again live with the new code: `run_v7_check.bat` does that.

**v8 re-measure (2026-10-05).** With the v8 code the whole table reads **20 / 20 in every one of the 11 cases** (220 / 220; median 2 calls, integer division included), and the impossible control **0 / 5**. Running the 220 derived programs (`v8cases_cross_check.txt`): all correct except one integer-division program that reads `q` before assigning it — legal in the calculus, where every variable always holds some value and the proof covers all of them, but a `NameError` in Python; the v9 copy gives such variables a start value in the emitted program.

### 5f. Z3 is lucky or unlucky `[ran]`

Found while checking, by hand and without any model, that the 12 HumanEval pilot problems can be derived at all. For the loop body of a primality check (`HumanEval/31`) the engine answered `unknown: timeout` after 10 s... on most runs. Run again, the identical derivation was sometimes proved in a second. Six repeats at the default limit: five rejected, one proved. The text sent to Z3 was byte-for-byte identical in every run (same checksum); the difference is inside Z3, whose search depends on how its terms happen to be numbered and on its random seed. With the text fixed and only the seed changed, **7 of 12 seeds proved the obligation in under 10 milliseconds and 5 timed out at 3 seconds.** A heavy-tailed running time like this is exactly where one long run is the wrong strategy.

So the prover (`FormalLLM/verification/z3_backend.py`, `_plan` and `_solve`) now tries an obligation in up to four short runs, each rebuilt from scratch with its own random seed (a tenth of the time limit, at least 0.3 s), and then in one patient run with the whole limit. Only calls that use the default limit do this (a model's proposal, not the assist's hundreds of cheap guesses); `FORMALLLM_Z3_RETRIES=0` turns it off. It cannot make anything unsound: a proof is a proof whatever the seed, and a counterexample from any run is reported as before.

Effect on the two hard pilot derivations (`16`, §5.2): `HumanEval/31` and `HumanEval/13` went from mostly *rejected after 10 s* to *proved in about 2 s* in every run (3 of 3 each, after the final design; the first design proved 4 of 4). An obligation Z3 truly cannot decide (it says `unknown: incomplete quantifiers`) is not retried at all. What it does not change: every stored result replays identically (398 of 399), so no recorded outcome depended on this luck, and the tests in `tests/test_z3_restarts.py` pin the behaviour (a timeout is retried, an unknown of another kind is not, a caller-given limit means a single run, a counterexample found by a later run is still reported).

The lesson for reading earlier numbers: a step that once ended `unknown: timeout` may have been a bad draw, not a hard goal.

---

## 5b. Efficiency: where the time goes `[ran]` (99 successful trials of the v5 run)

You also asked about efficiency. For a successful square-root derivation:

| | median |
|---|---|
| LLM calls | **2** (maximum seen: 11) |
| seconds per LLM call (`reasoning_effort = low`) | 6.2 s (about 180 output tokens per derivation) |
| wall time per derivation | **13.3 s** |
| — of which waiting for the model | 13.2 s (**99.5 %**) |
| — of which everything else: the search, Z3 on every step, the leaf assist, the feasibility checks | **0.06 s** |
| Coq re-checking the whole derivation afterwards | 2.7 s |
| Lean re-checking it (one process for all obligations) | ≈ 10–15 s |

So **Z3 and the whole refinement machinery are not the bottleneck; the model's latency is.** Efficiency therefore comes from asking the model *fewer times*, not from faster proving:

* the **leaf assist** removes the calls for the two trivial leaves (`x := 0`, `x := x + e`): without it each is a two-call round trip;
* **telling the right step what is wrong** removes the long wandering runs (the old code's slow successes took 19–22 calls);
* **`reasoning_effort = low`** makes each call about 3× cheaper than the model's default (≈ 24 s) with no measured loss of reliability on this task (medium effort is measured in the arms below);
* **batching** Lean's obligations into one process turns ≈ 10 s per obligation into ≈ 10 s per derivation.

---

## 6. What the numbers do not show

* **One model family, and mostly easy problems.** The square root (§5) and the 11 other solvable cases (§5e) were all run with `gpt-oss:120b` at low effort. Ten of those 11 passed at 20 of 20 with code whose fixes came from square-root failures, which argues against overfitting; but three of them (C1, C3, C4) have specifications a trivial program satisfies, so the loop evidence is thinner than the count suggests. The one failure, integer division, was fixed by reading *its* failures, so its re-measure shows the fix works, not that the method generalises. Open: a genuinely new problem set (the HumanEval pilot, `16`) and a second model.
* **The assist is not in the paper.** Without it the model must find the two trivial leaves (`x := 0`, `x := x + e`) itself, and it sometimes answers a leaf with another loop. Both arms are reported.
* **The termination rule matters.** The default strict rule (`0 ≤ V < V0`) rejects the natural variant `N − (x+e)²` (it goes negative on the last iteration); the paper's Lemma 6.7 accepts it. This is decision D1 in `12`, still open.
* **Low reasoning effort.** The model's default effort costs about three times as long per call; it is measured in the medium-effort arm.
* **A passing derivation is correct for the specification, not necessarily for the intent.** Here the specification is the paper's; for other problems that gap is what `16` is about.

---

## 7. How to repeat it

See `17`, §3. In short:

```bash
python benchmarks/reliability.py --config gpt-oss-120b-low --trials 100 --turns 2 --budget 30 \
       --strict 0 --assist --certify coq --label my_run
python benchmarks/replay.py "benchmarks/results/reliability/my_run_*.jsonl" --assist --strict 0

# the other benchmark cases, 20 trials each, one table at the end (resumable; see 17, section 3)
python benchmarks/reliability_batch.py --trials 20

# re-measure integer division after the assist fix, then the impossible-spec control (Windows: run_v7_check.bat)
python benchmarks/reliability_batch.py --prefix v7 --cases D1-intdiv A4-impossible
```

---

## Check yourself
1. Why can 30 successes out of 30 not show that the failure rate is zero? *(Only a bound: with 95 % confidence the success rate is at least ≈ 89 %.)*
2. What changed between the 7/10 and the 29/30 code: the prompt or the feedback? *(The feedback: who is told what after a failure.)*
3. Why can the loop body not repair a missing `x ≥ 0` itself? *(The body's precondition is built from the loop invariant its parent chose; only the parent can change it.)*
4. What does "feasible" mean for a specification, and why is an infeasible one hopeless? *(Every state satisfying the precondition has some final state satisfying the postcondition; otherwise no program can refine it.)*
5. Why is the assist reported as a separate arm? *(It is not in the paper's pipeline; its effect must be measured, not assumed.)*
6. Why was integer division the only failing problem, when the model chose the right loop every time? *(The loop's two child goals each needed two assignments in a row; the assist closed only one-line goals, and the model kept choosing a wrong middle assertion.)*
7. Why can Z3 answer `unknown: timeout` on one run and prove the very same obligation on the next? *(Its search depends on term numbering and its random seed, and its running time on hard goals is heavy-tailed, so a few short restarts beat one long run.)*
