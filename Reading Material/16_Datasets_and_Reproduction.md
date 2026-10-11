# 16 — Datasets and Reproduction: what can honestly be reproduced

> **Your requirement:** "finally the exact reproducible results on the datasets." This file says precisely what the paper measures, which parts could be rebuilt, which could not and *why*, and what the numbers are. It is deliberately blunt about scope, because a table that looks like the paper's but measures something smaller would be worse than no table.
>
> **Evidence tags:** `[ran]` measured here · `[read]` read in code/paper · `[test]` a unit test enforces it.
> Read `11` (the paper) first. Commands: `17`, §4.

---

## 1. What the paper measures `[read]`

| Paper | What | Our counterpart |
|---|---|---|
| **Table 6** | how many of the **164 HumanEval** programs pass all tests, on the original tests and on **EvalPlus** (≈ 80× more tests); GPT-4 alone: **145 / 128**; Refine4LLM: **150 / 150** | the direct-model baseline on all 164 (§4); the refinement pilot on the subset we can specify (§5) |
| **Table 7** | steps and proof time on classic programs (CorC), core laws vs extended laws | `benchmarks/classic.py`, 4 of the paper's programs (§6) |
| **Table 8** | effect of the **library** of learned laws | not reproduced: no learned-law library exists in our code (`12`, gap G-library) |
| **Table 9** | ablation (untuned GPT-4 → instruction-tuned → full) | not reproduced: no fine-tuned model |

---

## 2. Why "exact" is not possible, and what replaces it `[read]`

An exact reproduction needs three things the paper does not release (or that cannot be repeated):

1. **The formal specifications of the HumanEval problems.** The paper says they were "adapted from the BigCode project and manually checked" (§9.1); they are not in the paper. **Question for Dr. Hou (Q2): can he share them?** Everything in §5 uses specifications *I* wrote.
2. **The fine-tuned GPT-4 and the learned-law library.** Not available.
3. **A deterministic model.** A language model gives different answers on different runs, so even with the same specifications two runs differ.

What *can* be made exactly reproducible is everything **after** the model: every result file stores the model's raw replies, and `benchmarks/replay.py` feeds them back to the code offline; the same derivation, the same program and the same Coq/Lean verdicts must come out (§7). So "reproducible" here means: *given the stored replies, anyone can re-derive and re-check every number without the model.*

---

## 3. How much of HumanEval fits the language at all `[ran]`

The specification language (L_spec) has integers, floats, booleans, arrays you can read, `+ − × ÷`, comparisons and quantifiers; the program language (L_pl) has scalar assignment, sequencing, `if` and `while`. Classifying all 164 problems by what their test inputs and outputs actually are:

| Class | Problems | What it needs |
|---|---|---|
| **A** scalar result (number or True/False), numeric inputs | **53** | expressible today |
| **B** list result, numeric inputs | 28 | building arrays element by element (array writes) |
| **C** strings involved | 68 | strings and character operations |
| **D** dictionaries, tuples, nested lists | 15 | more data structures |

So **53 of 164 (32 %)** can be stated in the current language, and each still needs a hand-written specification. Many class-A problems also lean on `sum`, `len`, `%` or `sorted`, which the language has no names for. Extending the language (array writes, strings, a few built-in functions) is how coverage would grow toward the paper's 164; that is a research-size extension, not a bug fix.

---

## 4. The baseline rows: the model writes the programs directly `[ran]`

`gpt-oss-120b` (reasoning effort low, temperature 0) was given each of the 164 HumanEval prompts and asked for the function, with **no refinement and no prover** (`benchmarks/datasets/direct_baseline.py`). Each answer was run on the original HumanEval tests and on EvalPlus' roughly 80x larger test set; a problem counts only if *every* test passes. Raw answers and scores: `benchmarks/results/datasets/direct_baseline_gpt-oss-120b-low_rescored.jsonl`.

| | passes the original tests | passes the EvalPlus tests |
|---|---|---|
| paper, GPT-4 alone (Table 6) | 145 | 128 |
| paper, Refine4LLM (Table 6) | 150 | 150 |
| **`gpt-oss-120b` alone (ours)** | **156** of 164 (95.1 %, 95 % interval 90.7-97.5 %) | **147** of 164 (89.6 %, 84.0-93.4 %) |

**How to read it.** A modern open model working alone already beats the baseline the paper set out to improve, and passes *more* original tests than the paper's full method did; on EvalPlus it is 3 short of the paper's 150. So the paper's headline claim ("refinement lifts the model from 145/128 to 150/150") cannot be reproduced as "refinement beats the model alone": that gap has closed. What refinement offers now is something testing cannot: a **proof** that the program meets its specification for *all* inputs. The interesting question for this project has moved from "does it pass more tests?" to "does it get right the problems where a plausible program is wrong, and can the proof be trusted?".

Caveats, so the table is not over-read: a different model and a different year from the paper's GPT-4; one sample per problem at temperature 0 (the intervals only reflect which 164 problems there are, not the model's randomness); the paper's exact protocol is not public (question 4 for Dr. Hou, `18`).

**What it still gets wrong.** 8 problems fail the original tests (`HumanEval/24, 32, 101, 103, 106, 113, 116, 145`): two do not even compile (32 has a non-ASCII hyphen in a name, 101 an unterminated string) and six give wrong answers (for example `/24`, the largest divisor of 100, returned 10 instead of 50). Another 8 pass the original tests but fail EvalPlus' extra tests (`/50, 55, 86, 91, 97, 99, 132, 141`) and one (`/76`) times out there. I ran all 17 of these programs on the first input where they differ from the reference solution: 2 do not compile and 15 give a different answer or raise an error, so none is a scoring artefact of ours. A few EvalPlus failures penalise answers that are arguably *better* than the reference: for `/99` the reference loses precision on the 21-digit input `-578000000007654321.12345` (it answers `-578000000007654272`, the model `-578000000007654321`).

**A bug that made the first scoring 0 of 164.** The hosted endpoint answers in a forced JSON object by default, so the model's reply looked like `{"code": "python\ndef f(...): ..."}`. The code extractor only knew Markdown fences, so it ran the JSON text itself as Python, got a SyntaxError for every problem, and scored all 164 as failed (1563 of the 1570 original tests "failed"). Fixed in `humaneval.extract_code` (understands JSON replies, fences and a stray `python` first line); new baseline runs also ask the endpoint for plain text; `tests/test_extract_code.py` pins the shapes seen. The first scores are kept in `direct_baseline_gpt-oss-120b-low.jsonl` for the record; the corrected ones are in `..._rescored.jsonl`. Anyone can reproduce the corrected numbers offline: `python -m benchmarks.datasets.direct_baseline --reevaluate <file>` (about a minute, needs `evalplus`).

---

## 5. The refinement pilot: 12 problems, specifications checked against the reference solutions `[ran]`

### 5.1 The specifications, and how they were checked

Twelve class-A problems (`benchmarks/datasets/he_specs.py`), from trivial to hard:

| Tier | Problems |
|---|---|
| **A** (one assignment) | 41 `car_race_collision`, 157 `right_angle_triangle`, 138 `is_equal_to_sum_even` |
| **B** (a small search or loop) | 60 `sum_to_n` (a loop: its counter `i` is in the frame, see 5.2), 102 `choose_num`, 52 `below_threshold`, 35 `max_element` |
| **C** (nested quantifiers) | 13 `greatest_common_divisor`, 31 `is_prime`, 24 `largest_divisor`, 77 `iscube`, 0 `has_close_elements` |

A hand-written specification can be *wrong* (then every later result is about the wrong problem) or *too weak* (then a wrong program passes the prover). Both are checked mechanically, without any model, by evaluating the specification on concrete values (`FormalLLM/lspec/evaluator.py`):

* **Correctness:** for every original and EvalPlus test input, the reference solution's output must satisfy the specification. **12 of 12 do** (inputs whose quantifier range is too large to enumerate, e.g. gcd of two 9-digit numbers, are reported as *too large to check*, not as passed).
* **Strength:** each reference output is replaced by a wrong one (a boolean flipped, a number moved by 1 or doubled); the specification must reject it. **Every wrong output is rejected for all 12 specifications** (100 %).

These two checks caught real mistakes of mine: in the specification text language the negation `~` binds *weakest*, so `~(i = j) /\ rest` means `~((i = j) /\ rest)`; two specifications were wrong for that reason until the check failed on them.

### 5.2 Results

**First model run (2026-10-04 evening, before the v8 changes described in the newest entry of `10`; `gpt-oss:120b`, low effort, assist on, relaxed rule): 13 of 29 trials derived a program, and all 13 pass every original and EvalPlus test.** The run covered 10 of the 12 problems (`iscube` and `has_close_elements` were not reached) with two backends (`he_refine_z3.jsonl`: Z3; `he_refine_z3_lean.jsonl`: Z3 with Lean as the fallback). By tier: **A 7 of 9** (`car_race_collision` 3 of 3 and `right_angle_triangle` 3 of 3, two calls each; `is_equal_to_sum_even` 1 of 3), **B 6 of 14** (`sum_to_n` 5 of 5, `below_threshold` 1 of 2, `choose_num` 0 of 5, `max_element` 0 of 2), **C 0 of 6** (`greatest_common_divisor`, `largest_divisor`, `is_prime`: 0 of 2 each). Every failed trial used all of its 30 calls. The newest entry of `10` traces part of the shortfall to a display bug (the model was shown `n = 2 * n / 2` for `n = 2 * (n / 2)`), which that session fixed and re-ran: the numbers with the fix are in `19`, §4. For comparison, on these 12 problems the direct model passes **11 of 12** on both test sets and fails only `HumanEval/24` (`largest_divisor`); if refinement derives a verified program for that one, it fixes a real wrong answer.

**The v8 run (night of 2026-10-04/05; 20 problems: the 12 above plus 8 specified after the v8 fixes; every problem twice, the eight newest up to four times; 47 runs; files `he_refine_v8.jsonl` and `he_refine_v8_heldout.jsonl`).** 18 of 47 runs derived a program (8 of 20 problems at least once); **16 of those 18 programs pass every original and EvalPlus test**. By tier: **A 14 of 18** (`car_race_collision`, `triangle_area`, `add`, `is_equal_to_sum_even`, `right_angle_triangle` in *every* run at two model calls; `multiply` 0 of 4), **B 2 of 10** (`sum_to_n` 2 of 2; `max_element`, `below_threshold`, `choose_num`, `can_arrange` 0), **C 2 of 19, neither runnable**. The two unrunnable ones are valid proofs: `largest_divisor` used the proof-only constant `V0` in a test, and `iscube` assigned `t := (exists k. k*k*k = a)`; executing the derived programs is what exposed them, and both are refused in a v9 copy that is not yet measured (`20`, §7.5). Compared with the first run, the display fix raised `is_equal_to_sum_even` from 1 of 3 to 2 of 2, and the new type check removed the earlier `below_threshold` success, which had assigned `1` and `0` to a Boolean. Per-problem table: `python benchmarks/pilot_compare.py`; figure: `paper/fig_pilot.png`. **Reading:** with this untuned open model, refinement derives the simple problems reliably and rarely the loops and searches, although the engine accepts a hand derivation for 17 of the 20 — the gap is the model's search, and §7.5 of `20` lists what each failure was.

*Update (2026-10-05, 04:40 UTC, review session): the pilot has grown since: the 47 runs above, plus `he_refine_v7.jsonl` (a second set made at the same time with the same code), plus a third pass in `he_refine_v8.jsonl` that the model tunnel's monthly allowance cut short (rows 55 to 59 of that file were cut off by it and are stored as failures; the table now leaves them out, so it counts 121 real runs from 126 rows). Of the 121 real runs, 53 derived a program and 41 of those pass every original and EvalPlus test, for 7 of the 20 problems; I re-ran every derived program that can be run and got the stored results. Coq certified 45 of the 53 completely, including all 41 that pass; the 4 certified programs that do not pass cannot be run (they still contain a quantified statement), so no certified program gave a wrong answer. The other 8 could not be fully certified (Coq's tactics gave up on 13 steps, none was refuted): 4 of them cannot be run and 4 give wrong, too slow or never-ending programs (`largest_divisor`; `greatest_common_divisor` three ways). Table: `python benchmarks/pilot_compare.py --new benchmarks/results/datasets/he_refine_v8.jsonl benchmarks/results/datasets/he_refine_v8_heldout.jsonl benchmarks/results/datasets/he_refine_v7.jsonl`; the story is in `19`, §5, which now counts the same 121 runs.*

```bash
python -m benchmarks.datasets.he_refine --config gpt-oss-120b-low --repeats 3 --assist --out pilot.jsonl \
       --baseline benchmarks/results/datasets/direct_baseline_gpt-oss-120b-low_rescored.jsonl
```

**The ceiling, measured without any model (2026-10-04).** For a pilot problem to say anything about the *model*, the engine must be able to accept at least one derivation of it. `benchmarks/datasets/he_oracle.py` holds a derivation written by a person for eleven of the twelve problems. Each is applied law by law (every step proved by Z3), emitted as Python, wrapped as the HumanEval function and run on the original and the EvalPlus tests:

| Problem | The hand derivation | Z3 time | Original tests | EvalPlus tests |
|---|---|---|---|---|
| 41, 157, 138 | one assignment | under 0.01 s | pass | pass |
| 60 `sum_to_n` | a loop (`r := 0; i := 0; while i < n: i := i + 1; r := r + i`) | 0.3 s | pass | pass |
| 102 `choose_num` | three nested `if`s | 0.04 s | pass | pass |
| 52 `below_threshold` | a loop with a Boolean flag | 0.03 s | pass | pass |
| 35 `max_element` | the classic maximum loop | 1.5 s | pass | pass |
| 24 `largest_divisor` | search downwards from `n - 1` for a divisor | 0.7 to 1.7 s | pass | pass |
| 13 `greatest_common_divisor` | search downwards from `a` for a common divisor | 0.4 to 2.4 s | pass | **timeout** |
| 31 `is_prime` | trial division by `k = 2, 3, ...` up to `n` | 1.0 to 1.3 s | pass | **timeout** |
| 77 `iscube` | two search loops, for `a >= 0` and for `a < 0`, `k*k*k` against `a` | 2 to 4 s | pass | **timeout** |
| 0 `has_close_elements` | not derived by hand | | | |

Reading it.

* **Eleven of the twelve are known to be derivable by this engine**, so a model failure on them is a failure to *find* the derivation, not a limit of the engine. The one without an entry was not attempted (it needs two nested loops over floats with an existential over pairs); that is not a proof that no derivation exists. Z3 even proves the monotonicity of `x*x*x` that the cube search needs.
* **Three derivations are proved correct but too slow.** A downward search for a common divisor, trial division up to `n` and a search for a cube root are right, and the prover says so, but EvalPlus tests `gcd` on numbers near 2.5 x 10^12 and primality near 10^10, where those loops cannot finish in the time limit. The specification says what is true, not how fast; "proved correct" and "fast enough" are different properties and only the first is proved. A fast derivation (Euclid's algorithm; trial division only up to the square root) needs a nonlinear lemma: I tried the square-root version of `is_prime` and Z3 gives up on its last step. Whether Lean can prove it (`--backend z3+lean`) is open, and it is exactly what the fallback is for.
* **Why `HumanEval/60` was changed.** It originally had only `r` in its frame, so the only program the specification could express was the closed form `r := n * (n + 1) / 2`, whose proof needs "one of `n` and `n + 1` is even", a lemma no prover here has (`15`, §5). With the loop counter `i` in the frame, the loop above is proved in 0.3 s, and the closed form is still there for the model to try first. The specification is checked as before (12 of 12 agree with the reference solutions on every test input).
* **Z3 had to be made less unlucky for this to work.** The loops for `is_prime` and `gcd` were first rejected after 10 s on most runs and proved in a second on others; that is why the prover now restarts (`14`, §5f). Both go through in about 2 s.

**What was expected before the first run.** Tier A (three single assignments): near 3 of 3 in a few calls each. Tier B (four problems): the model has to choose a loop invariant or the right case split; the hand derivations are short, so most should be found, with a few calls more. Tier C: where the real information is. A verified-but-slow program counts as a derived program and fails the EvalPlus tests by timeout, which is a finding about specifications that say nothing about speed, not about the model. Run tier A first (`run_humaneval_pilot.bat --tasks A --repeats 1`, a few minutes), then B, then C; for C add `--backend z3+lean` so that goals Z3 cannot decide go to Lean. The first run (above) matched this for `car_race_collision` and `right_angle_triangle` and fell short elsewhere.


---

## 6. Table 7: classic programs, core laws vs extended laws `[ran]`

Four of the paper's classic programs (Factorial, Exponentiation, Linear Search, Max Element), each derived **twice** with a hand-written reference derivation: once with the core laws only (`sequential` + `iteration`), once with the extended law `initialised_iteration` that the paper learns. These are *scripted* derivations — no model — so the table shows what the **calculus** gives (depth and proof effort), not what a model finds.

| Problem | Steps core / extended | Our steps vs the paper's CorC / Initial / Refine4LLM | Proof obligations | Z3 time (s) | Coq certified | Lean certified |
|---|---|---|---|---|---|---|
| Factorial | 8 / 7 | 5 / 5 / 3 | 5 | 0.04 | 3 of 5 | **5 of 5** |
| Exponentiation | 8 / 7 | 7 / 7 / 5 | 5 | 0.03 | 3 of 5 | **5 of 5** |
| Linear Search | 8 / 7 | 5 / 5 / 4 | 5 | 0.05 | 2 of 5 | **5 of 5** |
| Max Element | 10 / 9 | 9 / 10 / 5 | 6 | 1.4 – 1.9 | 1 of 6 | **6 of 6** |

Reading it: the extended law removes exactly **one step** in every program (the separate set-up step is folded in), the same direction as the paper but a smaller effect (the paper's Refine4LLM column also uses more of its learned laws, and its step counting differs). Lean certifies all 21 obligations per calculus, Coq 9 of 21 — the difference is quantifier and array reasoning (`15`, §5.1). Three more of the paper's programs are *stated but not derived*: Logarithm (Z3 answers `unknown`), Dutch Flag Sort (needs array writes), Pattern Matching (needs strings).

---

## 7. Reproducing and replaying `[ran]`

```bash
# 1. the harness accepts all 164 reference solutions (should print 164 / 164 and 164 / 164)
python -m benchmarks.datasets.humaneval

# 2. the specifications are correct and strong
python -m benchmarks.datasets.he_specs

# 3. re-derive any stored study from its raw model replies, offline
python benchmarks/replay.py "benchmarks/results/reliability/v5_relaxed_assist_*.jsonl" --assist --strict 0 --certify coq

# 4. re-score the stored direct-baseline answers (no model; needs evalplus)
python -m benchmarks.datasets.direct_baseline --reevaluate benchmarks/results/datasets/direct_baseline_gpt-oss-120b-low.jsonl

# 5. the ceiling of the pilot: hand derivations through the engine and the real tests (no model; needs evalplus)
python -m benchmarks.datasets.he_oracle
```

A defect found on the way, relevant to every "does the program pass the tests?" number: the code that turned a derived program into Python used `/` for every division, but the prover reads `/` on two integers as **whole-number** division. A derived evenness test `n = 2 * (n / 2)` — proved correct — was, as Python, true for every `n` (`n = 9` gave `True`). The new emitter (`FormalLLM/lpl/typed_python.py`) uses `//` where both operands are integers, and `tests/test_typed_python.py` pins the example.

---

## 8. What would be needed to go further

| To cover… | Add |
|---|---|
| list-valued results (28 problems) | array assignment `a[i] := e` in the program language and a law for it |
| strings (68) | a character/string type and a few operations |
| `sum`, `len`, `%`, `sorted` | either built-in functions with axioms, or auxiliary arrays with defining axioms (as `classic.py` does for `fact`) |
| the paper's library of learned laws (Table 8) | a law-learning step (the paper's §6); not started |
| the paper's exact specifications | Dr. Hou's files (Q2) |

---

## Check yourself
1. Why is an exact reproduction of Table 6 impossible even in principle without the authors' files? *(The formal specifications and the fine-tuned model are not public, and a model is random.)*
2. What does it mean that a specification is *too weak*, and how was that tested? *(A wrong program would pass the prover; each reference output was replaced by a wrong one and the specification had to reject it.)*
3. How many of the 164 problems can the current language state? *(53, by signature; 12 have been specified so far.)*
4. What went wrong with `n = 2 * (n / 2)` when a derived program was run, and how was it fixed? *(Python's `/` is exact; the prover's is whole-number for integers; the emitter now uses `//` where both sides are integers.)*
5. What does `replay.py` reproduce and what can it never reproduce? *(Everything after the model's answers; never the model's answers themselves.)*
