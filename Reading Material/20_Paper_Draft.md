# 20 — Paper draft (for discussion with Dr. Hou)

> **What this is.** A first draft, written as a workshop/short paper, of what this project can claim *today*, with every number traceable to a result file in `benchmarks/results/` and a command in `17`. It is meant to be argued with, not submitted as is. The numbers are from the overnight runs of 2026-10-04/05 (see `19` for the summary); a row still marked **[PENDING]** was not finished by the morning.
>
> **For you (newcomer reading).** You do not need to read this before `19`. This file is the same material arranged the way a paper is: claim, method, evidence, limits. Where it says "we", read "this project".

---

## Title (working)

**Making LLM-Guided Program Refinement Reliable: Engine-Side Feedback, Faithful Presentation, and Cross-Prover Certification — a Reproduction Study of Refine4LLM with an Open Model**

## Abstract

Refine4LLM (Cai, Hóu et al., 2024) derives programs from formal specifications by letting a large language model (LLM) choose refinement-calculus laws and their parameters while a prover checks every step; on HumanEval it reports 150/164 verified programs passing both the original and the EvalPlus tests. We reimplement the approach with an open-weight model (`gpt-oss:120b`, low reasoning effort), Z3 for the search and Coq and Lean 4 as independent certifiers, and ask a question the original evaluation leaves open: *how reliably* does such a system succeed when a run is repeated? On the paper's own running example (integer square root by refinement) our first general-purpose implementation succeeded in 7 of 10 runs. Reading every failed transcript, we traced the failures not to prompt wording but to what the engine tells the model after a failed step (feedback addressed to the wrong node, misleading evidence, infeasible or meaningless sub-goals, ill-typed or unexecutable steps, and a renderer that showed the model a formula with a different meaning from the one the prover checked). Fixing these in the engine — none of them is specific to the example — raised the success rate to 99/99 (95% CI 96–100%), and the final code to 100/100, with a median of 2 model calls; all 11 further benchmark problems succeed in 20/20 runs each (220/220), and an impossible specification used as a negative control never succeeds. We also find three silent semantic mismatches between the search prover and the certifiers (integer division rounding, float arrays modelled as integers, Booleans coerced to integers) and close them with property tests. Finally we build 20 HumanEval specifications that are checked against the reference solutions on every HumanEval and EvalPlus input and mutation-tested, and find that two 2025 open models *alone* already pass 156/147 and 154/147 of the 164 problems — above the paper's GPT-4 baseline (145/128) — so the contribution of refinement today is the guarantee, not the pass rate. On those 20 problems refinement with the untuned open model derives verified programs reliably for the simple ones (41 of 121 runs yield a verified program that passes every test, all Coq-certified; 7 of 20 problems) and rarely for loops over arrays or nested-quantifier searches. Executing the derived programs exposed further gaps between proof and execution, one step that the search prover accepted although it is false — which Coq refused to certify and the tests caught — and a gap in the relaxed termination rule: over the integers, a measure that only has to decrease can decrease for ever, and a never-ending loop was 'proved'. We close it with an obligation that keeps the paper's measure admissible.

---

## 1. Introduction

LLMs write code that is usually plausible and sometimes wrong, and tests can show the presence of bugs but not their absence. Refine4LLM proposes a principled alternative: start from a formal specification `x : [P, Q]`, let the LLM pick a law of Morgan's refinement calculus and fill in its parameters (an intermediate assertion, a guard, a loop invariant and variant), and have an automatic prover discharge the law's side condition. A step that does not verify is rejected with the prover's counterexample; when every leaf is a primitive statement, the leaves compose into a program that is correct by construction.

The original evaluation reports *one* run per problem with a fine-tuned GPT-4, a learned law library and Coq/CoqHammer. Three things limit what such a number tells a reader: an LLM is stochastic, so one run is one sample; the HumanEval formal specifications were written by the authors and are not public; and the baseline it improves on (GPT-4 in early 2024) has since moved. We ask:

* **RQ1 (reliability).** On the paper's own running example, how often does an LLM-guided refinement search succeed, and what makes it fail?
* **RQ2 (generality).** Do the fixes found on that one example carry over to other problems, without re-tuning? Does the system ever "prove" an impossible specification?
* **RQ3 (datasets).** On HumanEval problems that the specification language can express, with specifications that are *checked* rather than trusted, what does refinement add over the same model writing code directly?
* **RQ4 (soundness of the tool chain).** Do the search prover, the certifiers and the executed program agree on what a specification means?

**Contributions.**

1. A **reproducible reliability protocol** for LLM-guided refinement: many independent trials per configuration, Wilson 95% intervals, every model reply stored so that every trial can be replayed bit-for-bit offline (`benchmarks/replay.py`), and network-lost trials separated from method failures.
2. A **taxonomy of ten failure classes** (F1–F10) read from failed transcripts, each fixed by a *general* check or feedback rule in the engine rather than by prompt wording; their effect is measured cumulatively, code version by version, plus three targeted ablations (leaf assist, termination rule, old vs fixed renderer) (§4, §7.2).
3. **Faithful presentation as a correctness property.** The text the model reads must mean what the prover checks. We found a renderer that dropped semantically necessary parentheses (`2 * (n / 2)` shown as `2 * n / 2`) and turned every parity test of the HumanEval subset into a tautology for the reader; a round-trip property test now guards the renderer (§4.3).
4. **Cross-prover semantic alignment.** Z3 (search), Coq and Lean (certification) and Python (execution) disagreed on integer division by negative numbers, on arrays of floats and on Booleans; we align them and pin each with tests (§5).
5. **Validated HumanEval specifications.** 20 specifications, each checked against the reference solution on every HumanEval and EvalPlus input (83–1011 inputs each) and mutation-tested (all 590 mutated outputs rejected), with hand-written reference derivations for 17 that the engine accepts step by step (§6).
6. An **updated baseline**: two 2025 open models alone already pass 156/164 and 154/164 (HumanEval) and 147/164 (EvalPlus), so for current models the value of refinement is the proof (§7.3).
7. **A termination gap and its repair**: the relaxed rule (`V < V0`) is unsound for integer measures; adding `I ∧ G ⇒ 0 ≤ V` makes it sound and keeps the paper's measure `N − (x+e)²` admissible (§7.5).

## 2. Background: the refinement calculus as used by Refine4LLM

A specification `x : [P, Q]` may change only the *frame* variables `x`; starting in any state satisfying `P`, it must terminate in a state satisfying `Q`. A law replaces it by a program or by smaller specifications, provided a side condition holds. The laws used here (paper §2.2 and §6.2):

| Law | Rewrites `x : [P, Q]` to | Side condition |
|---|---|---|
| skip | `skip` | `P ⇒ Q` |
| assignment | `x := E` | `P ⇒ Q[x := E]` |
| sequential | `x : [P, R] ; x : [R, Q]` | none (R chosen) |
| alternation | `if G then x : [P ∧ G, Q] else x : [P ∧ ¬G, Q]` | none |
| iteration / initialised iteration | (set-up `x : [P, I]` ;) `while G do x : [I ∧ G ∧ V = V0, I ∧ 0 ≤ V < V0]` | `I ∧ ¬G ⇒ Q` (and `P ⇒ I`) |
| strengthen post / weaken pre | `x : [P, R]` / `x : [R, Q]` | `R ⇒ Q` / `P ⇒ R` |

The termination condition `0 ≤ V < V0` is our default ("strict"); the paper's Lemma 6.7 uses `V < V0` together with the invariant ("relaxed"). Which one is the default is an open design decision (D1 in `12`); results below state the rule used.

## 3. System

**Search.** A two-turn protocol per node: (1) the model chooses a law from cards that state each law's rule, parameters and when to use it; (2) it supplies the parameters. The engine applies the law, generates proof obligations and sends them to Z3. A rejected step returns the counterexample, the violated part of the goal, and advice addressed to the step that can fix it. Each node owns a call allowance (10 calls below a step; 30 per trial in total).

**Certification.** When a derivation is complete, its obligations are re-checked by Coq (Rocq 9.1, standard tactics plus CoqHammer's `sauto`) and/or Lean 4 (Mathlib, `grind`/`omega`, all obligations of a derivation in one process). A `z3+lean` backend asks Lean only when Z3 answers *unknown*, and accepts only a kernel-checked proof.

**Leaf assist (optional, reported as a separate arm).** Most nodes of a derivation are not creative: after the model chooses a loop, the set-up and the body are usually one or two assignments. The assist tries a fixed family of short assignments built from the specification's own names (and an expression solved from an equation of the postcondition, e.g. `r := n − q·d`), and two assignments in a row via the weakest precondition of the second. Every candidate goes through the same engine and prover as a model's proposal, so the assist adds no trust; it only saves calls. It is not in the paper and is reported on/off.

**Execution.** The finished derivation is emitted as Python using the specification's declared types (`//` where the prover reads whole-number division), wrapped as the HumanEval function and run on the original and EvalPlus tests.

## 4. Why runs fail, and what fixed it (RQ1)

### 4.1 Protocol

Each configuration is run for N independent trials (N = 10 … 100) with the same model (`gpt-oss:120b`, `reasoning_effort = low`, temperature 0.2), budget (30 calls) and protocol; a trial succeeds if the root specification is completely refined. We report successes, the Wilson 95% interval, median and maximum calls, and wall time. Every reply is stored; `replay.py` re-derives a trial offline and must reproduce its outcome exactly (it does, for 398 of 399 stored trials; the exception is explained in `14`).

### 4.2 Failure classes

Table 1 lists the failure classes, how each manifested, and the general rule that removed it. F1–F6 were found on the square-root example; F7–F10 on the other benchmark problems and the HumanEval subset.

| # | Failure (observed) | General fix in the engine |
|---|---|---|
| F1 | advice addressed to a node that cannot act on it (loop body told to "strengthen the invariant") | per-obligation advice; the body returns to its parent with the missing fact |
| F2 | parent shown the system's own probe of another node as evidence | failure digest follows the failed child; probes excluded |
| F3 | a step's call allowance exhausted, step declared dead | allowance owned by a step; the owner may propose again |
| F4 | invariant makes the loop body infeasible | every sub-specification must be feasible (∀ pre-state ∃ post-state); refused with values |
| F5 | model invents a name (`V`) the prover reads as a free constant | vocabulary check: only the specification's names |
| F6 | split on a variable whose entry value is arbitrary | refused with explanation; call allowance 16 → 10 |
| F7 | a correct loop whose set-up/body need two assignments: the model's middle assertions are wrong | assist: equation solving and two-assignment search via weakest precondition (bounded by prover queries, not seconds) |
| F8 | **presentation**: `2 * (n / 2)` rendered as `2 * n / 2` (a tautology to the reader) | renderer keeps value-changing parentheses; round-trip property test |
| F9 | quantifier syntax variants (`forall k:int (...)`, `->`) rejected with raw parser errors | binder spellings normalised; actionable hint; syntax shown in the language card |
| F10 | proved but unusable steps: a quantified `if` test (cannot run); `b := 0` for a Boolean (accepted by Z3's Int/Bool coercion) | guards must be quantifier-free; assignments are type-checked |

The improvement from v3 (7/10) to v6 (99/99) is far beyond trial-to-trial noise (two-sided Fisher exact test, p = 0.0006). The key observation of RQ1 is that **the fixes that mattered are about what the engine checks or says after a failure, not about the prompt's instructions**: the jump from 7/10 to 29/30 came from changing only the feedback (F1–F3 and the missing-fact diagnosis), with the same prompt (`14`, §3).

### 4.3 Faithful presentation (F8)

The model never sees the prover's internal formula; it sees a rendering with minimal parentheses. A rendering is *faithful* if parsing it back yields a formula with the same value everywhere. Our renderer parenthesised a same-level right operand only under `−` and `/`; under `*` it dropped the parentheses of a right operand that contains a division. With whole-number division, `2 * (n / 2) = n` ("n is even") and `2 * n / 2 = n` (always true) differ, and every parity and divisibility condition of the problems in the earlier pilot runs (`choose_num`, `is_equal_to_sum_even`, `greatest_common_divisor`, `is_prime`, `largest_divisor`) was shown to the model with the second meaning. Transcripts show the model reasoning from the wrong meaning ("`g := 1` satisfies `a = g * a / g` trivially") while the prover, correctly, refuted it. The fix is one line; the lesson is a test: 300 random arithmetic trees, rendered and parsed back, must evaluate identically on random inputs (`tests/test_spec_render.py`).

### 4.4 Results

| Code | What changed | Successes (square root, relaxed rule, assist on) | 95% CI | Calls, median (max) |
|---|---|---|---|---|
| v1 | general prompt, bug fixes | 9/10 | 60–98% | 2 |
| v3 | + credit assignment, subtree cap | 7/10 | 40–89% | 2 or 19–22 |
| v4 | + F1–F3, missing-fact diagnosis | 29/30 | 83–99% | 2–5 |
| v5 | + F4, F5 | 99/100 | 95–100% | 2 (11) |
| v6 | + F6 | 99/99 (1 trial lost to the network) | 96–100% | 2 (9) |
| v8 | + F7–F10, prover alignment (§5) | **100/100** (two independent sets of 50) | 96–100% | 2 (4) |

## 5. Do the provers agree on what the specification means? (RQ4)

A derivation is searched with Z3, certified with Coq and Lean, and executed as Python. If these read the same formula differently, a "certified" program can be wrong, or a correct step can be rejected. We found three mismatches, none of which had shown up in any benchmark result:

| Construct | Z3 (before) | Coq | Lean | Python | Fix |
|---|---|---|---|---|---|
| `a / b` on integers, `b < 0` | Euclidean (`7 / −2 = −3`) | floor (`−4`) | floor (`Int.fdiv`, `−4`) | floor (`−4`) | Z3 encodes floor division; a divisibility test `x = k * (x / k)` keeps native division (it does not depend on rounding, and the case split made quantified searches time out) |
| `array float` | `Array(Int, Int)`: a step valid only for integers (`a < b ⇒ a + 1 ≤ b`) was accepted for floats | reals | reals | floats | element sort from the declared type |
| `b := 0`, `b : bool` | accepted (z3py coerces `false` to 0) | — | — | runs only because `0 == False` | assignments type-checked; the assist proposes `true`/`false` |

Each fix is pinned by a test that fails on the old behaviour (`tests/test_z3_semantics.py`, `tests/test_value_kinds.py`). Replaying the 99 stored square-root trials that reached the model through the aligned prover reproduces every one of them exactly (same outcome, same number of calls, same program), so no earlier square-root result depended on the mismatches.

## 6. Checked specifications for HumanEval (RQ3, part 1)

The paper's HumanEval specifications are not public, so we wrote our own and **checked them mechanically** rather than by inspection:

* **Expressibility census.** Of the 164 problems, 53 have numeric inputs and a scalar result (the rest need strings, lists as results, or dictionaries); many of the 53 need `sum`, `len` or `pow`, which the specification language does not have. We specified the 20 that need none of these.
* **Correctness.** For every HumanEval and EvalPlus input, the reference solution's output must satisfy the specification, evaluated exactly (`FormalLLM/lspec/evaluator.py`; bounded quantifiers enumerated; inputs whose ranges are too large are reported as unchecked, not as passing). All 20 pass on 83–1011 inputs each.
* **Strength.** Each reference output is replaced by a wrong one (Boolean flipped; number ±1 or doubled) and the specification must reject it: all 590 mutated outputs are rejected (147 for the first 12 specifications, 443 for the 8 added on 2026-10-04).
* **Derivability.** For 17 of the 20, a hand-written derivation is accepted by the engine step by step and its program passes every original and EvalPlus test, except three that are proved correct but too slow for EvalPlus's largest inputs (a linear search for `gcd`, primality, cube root). The remaining three (`has_close_elements`, `pairs_sum_to_zero`, `triples_sum_to_zero`) need nested loops over pairs or triples and were not derived by hand.

The checks caught real errors of ours: two specifications that misused the language's negation precedence, one that assumed Python's `% 10` where the reference takes the last decimal digit of |a|, and an evaluator that decided division from runtime values instead of declared types.

## 7. Evaluation

### 7.1 RQ2 — generality on the other benchmark problems

Same model and settings, 20 trials per problem, Coq certification on; `A4` is an impossible specification (negative control).

| Case | v6 code (2026-10-04) | v8 code |
|---|---|---|
| A1–A3, B1–B3, C1–C4 (10 problems) | 200/200 (each 20/20) | **200/200** (each 20/20, all Coq-certified) |
| D1 integer division (two variables, loop) | 1/20 (before the two-assignment search existed) | **20/20** (median 2 calls) |
| A4 impossible (control) | 0/5 (sound) | **0/5** (sound) |

A second complete run with the same v8 code (a launcher that kept running in parallel; files `v7cases_*` dated 2026-10-05) gave **220/220 and 0/5 again**; there Coq certified 218 of the 220 derivations (on two division derivations its tactics could not close one step; nothing was refuted).

### 7.2 RQ1 ablations

| Arm | Successes |
|---|---|
| v6, strict termination rule (`0 ≤ V < V0`), assist on | **46/48** (96 %, CI 86–99 %; 2 more trials lost to the network); median 3 calls, 21 s (relaxed: 99/99, 2 calls, 12 s); Fisher p = 0.11 vs relaxed — the strict rule costs time, not measurably success |
| v6, assist off | **8/30** (27 %, CI 14–44 %; Fisher p ≈ 2 × 10⁻¹⁸ vs 99/99); successes need a median of 19.5 calls; failures propose a loop law a median of 12 times where one suffices — the model chooses the right loop but answers the trivial set-up and body with further loops |
| v8, `reasoning_effort = medium` | **20/20** (median 2 calls; 32 s per trial instead of 21 s) |
| v8, assist off; second model on the square root | not measured: from about 09:10 on 2026-10-05 the tunnel to the model server answered every call with HTTP 403 (monthly bandwidth limit); the trials run then never reached a model and are excluded |

### 7.3 RQ3 — HumanEval: direct model vs refinement

**Direct model (all 164).** `gpt-oss:120b` at low effort, one sample per problem at temperature 0, no refinement: **156/164** pass the original tests and **147/164** pass EvalPlus; a second open model, `qwen3-coder-next`, gives **154/164** and **147/164** (paper, Table 6: GPT-4 145/128, GPT-4 + formal spec 148/142, Refine4LLM 150/150). On our 20-problem subset the direct model fails `largest_divisor` (24) on both test suites and `multiply` (97) on EvalPlus.

**Refinement on the 20 checked specifications** (v8, 121 runs: each problem 4 to 8 times, from two runs of the pilot made side by side with the same code; 5 further runs cut off by the server outage are excluded; a run counts if the derivation is complete, and its program is then run on the original and EvalPlus tests; per-problem table: `benchmarks/pilot_compare.py`; figure: `paper/fig_pilot.png`):

| Problem set | Old code (12 problems, 29 runs) | v8 (20 problems, 121 runs) |
|---|---|---|
| tier A (one assignment or case split; 6 problems) | 7/9 runs | **35/42** runs; 5 problems derived in every run at two model calls; `multiply` 1/8 |
| tier B (a loop or a chain of cases; 5 problems) | 6/14 runs | **7/29** runs (`sum_to_n` 6/6) |
| tier C (searches with nested quantifiers; 9 problems) | 0/6 runs | **11/50** runs, none of whose programs passes the tests (§7.5) |
| derived programs passing every original + EvalPlus test | 13/13 | **41/53**, all 41 fully certified by Coq (Coq fully certifies 45 of the 53: these 41 and 4 valid but unrunnable ones) |
| problems with a verified, test-passing program | 5 of 10 | **7 of 20** |
| held-out: the 8 problems specified after the v8 fixes | — | `add` 8/8, `triangle_area` 8/8, `multiply` 1/8; no runnable program for the other five |

With this untuned open model, refinement derives the simple problems reliably (every run, two model calls, every program passing every test) and rarely finds loops over arrays or nested-quantifier searches, although hand derivations exist for 17 of the 20 problems. One result goes beyond the model alone: for `multiply`, which the direct model gets wrong on EvalPlus, one run derived a verified program (25 calls) that passes every original and EvalPlus test. On the original twelve, the display fix raised `is_equal_to_sum_even` from 1/3 to 6/6, and the type check removed the earlier `below_threshold` success, which relied on assigning `1` and `0` to a Boolean.

### 7.4 Cost

For the square root, the median trial takes 12–13 s, of which 99.5% is waiting for the model; the search, Z3 on every step, the assist and the feasibility checks together take about 0.06 s; Coq re-checks a derivation in about 2.7 s and Lean in 10–15 s (one process for all obligations). Efficiency therefore comes from asking the model fewer times (the assist; feedback that prevents wandering), not from faster proving.

### 7.5 What the HumanEval failures teach

Every failed or suspicious pilot run was read. The failures fall into two groups, and only one of them is the model's.

**Proved but not runnable (found only because the derived programs are executed on the tests).** Nine v8 derivations are valid proofs whose programs cannot run: eight assign a quantified formula and one tests a proof-only name. Two examples:
* `largest_divisor`: inside the loop body the model split on `r = V0`, where `V0` is the proof-only snapshot of the loop measure at the start of the iteration. The precondition makes the test true, so the step is valid, but the emitted program reads `V0` and stops with `NameError` on every test. Root cause, measured: the leaf assist *does* find the right body `r := r − 1`, but Z3's success on this quantified divisibility goal depends on its internal state (the same query is proved inside the assist's search and answered `unknown` when asked alone, even with 10 s), and the assist's quick checks get no seed restarts; in the live run it missed, and the model was asked.
* `iscube`: `t := (∃k. k·k·k = a)` — a trivially valid assignment of a quantified formula, which no program can evaluate. v8 refused quantified *tests* but not quantified *values*.

**The model does not find the derivation (all have a hand derivation the engine accepts).**
* `choose_num`: the model insists on the test "an even number exists in [x, y]" (refused as unexecutable seven times in one run); twice it wrote a correct quantifier-free equivalent but then did not take the next split (on the parity of `y`).
* `multiply`: the model splits the `else` branch on its parent's test again and again; each new `then` branch has a contradictory precondition and is closed by `skip`, so nothing progresses (the engine's progress check only catches textually identical sub-problems).
* `max_element`, `below_threshold`: quantifier-scope errors in invariants (`… && forall (k:int) A || B && exists (j:int) …` without parentheses, so the `forall` swallows the `exists`), bounds copied from the specification instead of adapted (`k < i || k >= n` for "the prefix"), and an early-exit loop whose body must still decrease the measure. Array counterexamples were shown in Z3's internal notation (`l = Store(K(Int, 2437), 0, 2438)`).

**Two more gaps between proof and execution, found in the other runs.** A division derivation began with `r := n − q·d` before `q` was assigned: legal in the calculus (every variable always holds some value, and the proof covers all of them), a `NameError` in Python. The eight quantified assignments are counted under "cannot run" above.

**A step that should have been refused was accepted once.** In one `gcd` run the leaf assist closed the sub-problem [g > 0 ∧ g | a ∧ g | b, "g is the greatest common divisor"] with `x := g · k`. The obligation is false (a = b = 4, g = 1), so Z3 must have answered *proved* in that run; offline, the same obligation is answered *counterexample* or *unknown* in 41 of 41 tries with different seeds, replaying the stored run does not accept it, and four complete re-runs of the assist's search on that sub-problem (about 3,700 Z3 queries) accept nothing (their only *proved* answers have contradictory assumptions, which is correct). The derivation was **not certified by Coq** (0 of 2 obligations) and its program **failed the tests**, so the two independent safeguards caught it. It is the only such case found among the night's derivations; every derivation counted as a success in this paper is certified by Coq. Whether the cause is a solver fault under a long-running process or a state-dependent bug of ours is under investigation. Until it is known, the conservative reading — adopted throughout — is that a derivation is *verified* only when an independent kernel has certified it.

**A never-ending loop, proved under the relaxed termination rule.** All pilot runs used the relaxed rule, under which the loop measure only has to decrease (`V < V0`, Lemma 6.7 as we read it). In one `gcd` run the model's loop `while g is not a common divisor: g := g + 1`, with measure `a − g` and an invariant that does not bound `g` by `a`, was accepted: the measure decreases on every iteration. The program never stops when `a` does not divide `b` — `g` grows past `a` and the measure decreases for ever (the tests time out). Over the natural numbers `V < V0` suffices; over the integers it does not. We checked every loop the model proposed in a successful run (Z3: does `I ∧ G ⇒ V ≥ 0` hold?): all 265 checkable loops in the counted successes are bounded, so relaxed and strict coincide for every success reported here. The repair keeps `V < V0` and adds the obligation `I ∧ G ⇒ 0 ≤ V` (the measure is never negative while the loop runs). It is sound over the integers, refuses the `gcd` loop, and still accepts the paper's measure `N − (x+e)²`, which is negative only after the last iteration; under it, 90 of 90 stored square-root and loop derivations replay identically. This bears directly on decision D1 (which termination rule to adopt).

**v9 (implemented and unit-tested; not yet measured).** Six general rules follow, none specific to a problem: a test or assigned value may not mention a proof-only name; a quantified value is refused like a quantified test; a split whose test the precondition already decides is refused (one branch could never run); array values in counterexamples are shown element by element; the emitted program gives every frame variable whose starting value the specification leaves arbitrary a start value; and the relaxed termination rule requires the measure to be non-negative while the loop runs. Replaying the stored `largest_divisor` run through v9, the assist closes the body and the run succeeds in 2 calls with a runnable program. Prompt changes that the failures suggest (an array-scan example for the loop recipe) were deliberately *not* made: the eight problems added on 2026-10-04 were specified after the v8 fixes and serve as held-out problems, and tuning the prompt on them would contaminate the evaluation.

## 8. Discussion and limits

* **The baseline has caught up.** The paper's headline claim — refinement lifts GPT-4 from 145/128 to 150/150 — cannot be reproduced as "refinement passes more tests", because the open model alone passes 156/147. What a derivation adds is a machine-checked guarantee for *all* inputs that satisfy the precondition, and a program that does not degrade from HumanEval to EvalPlus. On our subset, every derived program that can run passes every original and EvalPlus test; two v8 derivations were valid proofs of programs that cannot run (§7.5), which only executing the derived programs revealed.
* **Termination needs care with integer measures.** The relaxed rule, as implemented, admitted a non-terminating loop (§7.5); its repaired form is sound and keeps the paper's measure. Whether the paper's measures are naturals is a question for its authors.
* **Coverage is the bottleneck, not the search.** 20 of 164 problems are specifiable in the current language. Strings, list-valued results and built-ins (`sum`, `len`) are a language extension, not a tuning problem; the paper's law library and fine-tuned model are not available.
* **Specifications are ours.** They are checked against reference outputs and mutation-tested, which catches wrong and weak specifications, but they are not the paper's. Q2 in `18` asks for the originals.
* **One model, low effort.** All numbers use `gpt-oss:120b` at low reasoning effort; medium effort and a second model are measured on small samples only.
* **Proved is not fast.** Three derived programs are correct but time out on EvalPlus's largest inputs; specifications say nothing about running time.
* **The assist is not in the paper.** Every result states whether it was on; on/off arms are reported.

## 9. Related work (to be completed with Dr. Hou)

* **Refinement calculus and correctness-by-construction:** Morgan, *Programming from Specifications*; Back and von Wright, *Refinement Calculus*; CorC (Runge et al.), the tool the paper compares against.
* **LLMs with verifiers:** Refine4LLM (Cai, Hóu, Sanán, Luan, Lin, Sun, Dong); Clover (closed-loop verifiable code generation with Dafny); Lemur (LLMs proposing invariants for program verifiers); Baldur (whole-proof generation and repair in Isabelle).
* **Benchmarks:** HumanEval (Chen et al., 2021) and EvalPlus (Liu et al., 2023).
* **Provers:** Z3 (de Moura and Bjørner, 2008), Coq/Rocq with CoqHammer (Czajka and Kaliszyk), Lean 4 with Mathlib.
* **Neuro-symbolic agents** (the papers collected in `Related Work/`): SymCode, neurosymbolic compliance with SMT solvers, natural-language formalisation and verification.

## 10. Reproducibility

Every number above comes from a file in `benchmarks/results/` and a command in `17`. Every trial stores the model's raw replies; `python benchmarks/replay.py <file> --assist --strict 0` re-derives it offline and reports whether the recorded outcome is reproduced. The HumanEval specifications are re-checked by `python -m benchmarks.datasets.he_specs`, the hand derivations by `python -m benchmarks.datasets.he_oracle`, and the test suite (`python -m pytest FormalLLM/tests -q`) has over 400 tests, including Coq and Lean checks.
