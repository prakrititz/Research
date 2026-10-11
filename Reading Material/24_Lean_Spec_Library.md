# 24 — The Lean specification library (all 164 HumanEval problems and 5 classic algorithms, stated in Lean)

> **Update 2026-10-11:** the library now has 169 specifications (164 HumanEval + 5 classics): 2,332 tests, reference 2,332/2,332, postcondition accepts 2,332/2,332 and rejects 5,651/5,657 wrong outputs (the 6 are one `permissive` dictionary specification). The sections below describe the first 42 (2026-10-08); the numbers in them are those of that date. Specifications live in `benchmarks/datasets/lean_specs.py` (the first 37) and `benchmarks/datasets/he_lean/` (the rest); see doc 22, entry 2026-10-11.

> Written 2026-10-08. Code: `benchmarks/datasets/lean_specs.py` (the table, the builder, the validator), `lean_taskfile.py` (writes Verina's file format), `lean_oracle.py` (hand-written derivations). Data: `benchmarks/datasets/lean_specs/<id>/`. Results: `benchmarks/results/lean_specs/`. Phase 4 of the plan in doc 22.

## 1. Why a second library

The first library (`he_specs.py`, doc 16) states a HumanEval problem in the earlier specification language. That language has integers, floats, booleans and read-only arrays, so only problems with number/boolean inputs and results are expressible: about 20 of the 164 problems, and the pilot used 20 of them. Everything that involves a list result, a string, a membership or "for all positions" was out of reach, and that is most of HumanEval. Lean states all of it, and the Verina benchmark uses Lean the same way. So the new library:

* is written in **Verina's file format** (`task.json`, `description.txt`, `task.lean` with the `-- !benchmark @start/@end` regions, `test.json`), so Verina's tasks and ours go through the same loader (`FormalLLM/lean/task.py`), evaluator (`benchmarks/verina_eval.py`) and engine;
* covers **lists (22 specs), strings (8), scalars (14), an option result (1), recursive specification functions (2)**, with 25 that need a loop; 5 are one-step (`term`) problems. Of the 42, 37 are HumanEval problems (one each) and 5 are classic algorithms written for this library (section 5).

## 2. How a specification is written

Example (`he_043_pairs_sum_to_zero`): *decide whether the list has two distinct elements that sum to zero.*

```lean
def pairsSumToZero_precond (l : List Int) : Prop := True
def pairsSumToZero_postcond (l : List Int) (result : Bool) (h_precond : …) :=
  result = true ↔ ∃ j, j < l.length ∧ ∃ i, i < j ∧ l[i]! + l[j]! = 0
```

The specification says **what**, never how: no loop, no accumulator. The reference solution (`(List.range l.length).any (fun j => …)`) is in the file only to test the specification; the engine never sees it (a test checks that the prelude it loads contains no `def f`).

Quantifiers use the shape Lean can *decide*: `∀ i, i < n → …`, `∃ j, j < n ∧ …`, `∀ x ∈ l, …`. That is a constraint on the author, and it buys the check below: the specification can be run on concrete values.

## 3. How a specification is checked (the same idea as doc 16)

`python benchmarks/datasets/lean_specs.py validate` imports all of Mathlib once (60–110 s) and, for every specification:

1. the file with its reference solution **compiles**;
2. the **reference solution passes every test** (`#eval f args == expected`);
3. the **postcondition accepts the expected output** of every test (`#eval decide (f_postcond args expected …)`): a specification that rejects the canonical solution's output is wrong;
4. the **postcondition rejects every wrong output**, built by mutating the expected one (Bool negated; number ±1 or doubled; string with a letter added or dropped or reversed; list with an element added, dropped or changed, or reversed; option none ↔ some; pair component changed): a specification that accepts them is too weak.

The tests of a HumanEval problem are **HumanEval's own inputs** that fit the size limits, plus an even spread of **EvalPlus' extra inputs**, with the expected outputs of HumanEval's canonical solution (read from the EvalPlus data, not recomputed). The classics have hand-written tests.

| | Result (2026-10-08) |
|---|---|
| Specifications | 42, all compile |
| Tests | 551 (5 to 23 per specification) |
| Reference solution passes | **551 of 551** |
| Postcondition accepts the expected output | **551 of 551** |
| Wrong outputs rejected | **1,201 of 1,201** |
| Not decidable (could not be run) | 0 |

### What the checks found (mistakes caught by the validator, all fixed)

* **`he_097_multiply`**: I had written the unit digit with Lean's `%` (always non-negative), which looked like Python's `a % 10`. Six of 16 tests failed in both the reference and the specification: EvalPlus' expected outputs use the unit digit of the **absolute value** (for `a = -14` the unit digit is 4, not the 6 that `-14 % 10` gives). The specification now uses `natAbs % 10`. This is the check doing its job: the specification and the reference agreed with each other and both disagreed with the data.
* **Strings with characters outside the basic plane** (an emoji in `he_028_concatenate`): the test harness escaped them as UTF-16 pairs, which Lean reads as two characters. Fixed in the REPL session (raw UTF-8) and in the literal renderer (`ensure_ascii=False`).
* A **`some (2)` expected value passed as an argument** without parentheses (`f_postcond args some (2) proof`): the validator parenthesises it now.
* Test selection filtered **large outputs** (a factorial) together with large inputs, leaving `he_139` with 3 tests; outputs are no longer size-filtered, only lists and strings.

## 4. Hand-written derivations ("oracles") — `lean_oracle.py`

For 36 of the 42 specifications a person wrote a derivation with the four laws (`term`, `cases`, `bind`, `loop`) and ran it through the engine of doc 23. This is not a model result: it shows which tasks are **within reach of the laws** and **where Lean's automation is too weak**.

| | Result |
|---|---|
| Derivations written | 36 (31 for HumanEval problems, 5 for the classics) |
| Accepted by the engine and **certified** (whole term compiles, `#print axioms` lists only the three standard axioms) | **36 of 36** |
| Tests passed by the derived programs | **475 of 475** |
| Laws used | 91 in total (1 law: 6 derivations; 2 laws: 23; 4: 3; 5: 1; 7: 2; 8: 1) |
| Time | 151 s for all 36 with all of Mathlib loaded, including the certification of each (mean 4.2 s) |
| Verina's own tasks (`verina_oracle.py`, written by other authors) | 19 of 20 certified, 109 of 109 tests |

Not written: `he_013` (gcd; needs a divisibility lemma), `he_016` (distinct characters), `he_034`/`he_058` (sorted unique lists), `he_090` (second smallest), `he_114` (minimum sub-array sum). They are the stretch targets for a model.

### Where the stock automation fell short, and what fixed it (the "lemma library")

The first run certified **20 of 25** (of the library as it then was). Each failure was an obligation that a person would call routine and the cascade could not close; each is now a proved lemma or a tactic alternative (`FormalLLM/lean/lemmas.py`, `engine.CASCADE`), and the oracle run is the regression test.

| Needed by | Obstacle | Fix |
|---|---|---|
| `below_threshold`, `max_element`, `is_sorted` (loop exit) | the invariant is by index (`∀ k < i, l[k]! < t`), the specification is by member (`∀ x ∈ l, x < t`); and `i = l.length` is only implied by `i ≤ l.length` and `¬ i < l.length` | `Refine.forall_mem_iff_idx`, `exists_mem_iff_idx`; the loop's exit proof first derives and substitutes `v = e` when the guard is `v < e` (`laws.with_bound`) |
| `max_element` (loop start) | `l.head! = l[0]!` | `Refine.head_bang_eq` |
| `below_zero`, `correct_bracketing` | `∃ k ≤ i + 1, P k` splits into `k ≤ i` or `k = i + 1` | `Refine.exists_le_succ`, `forall_le_succ` |
| `below_zero`, `get_positive`, `digit_sum` | one more element of a prefix: `take (i + 1) = take i ++ [l[i]!]` | `Refine.take_succ_bang`, `sum_take_succ_bang`; **plus removing the core lemma `List.take_append_getElem` from the simp set: it folds the prefix back and `simp` looped to the recursion limit (found with `trace.Meta.Tactic.simp.rewrite`)** |
| `digit_sum`, `correct_bracketing` (exit) | `s.toList.take s.length = s.toList` | `Refine.take_string_length`, `String.length_toList` |
| `solution`, `add_even_at_odd`, `get_positive` | `if … then acc + x else acc` against a filtered, mapped, summed `range (i + 1)` | tactic alternative `split <;> simp_all […]` and `List.range_succ` |
| `special_factorial` | `fact * (i + 1) = factSpec (i + 1)` (commutativity) | alternative with `Nat.mul_comm` |

Reading the table as a research result: **the unit of difficulty is not the program but the bridge between two ways of writing the same fact** (members versus indices; a prefix versus the next element; a guard versus an equality). The laws never failed; every rejection was a bridge. That tells us what to give a model: the bridges, as named lemmas it may cite.

## 5. The classic algorithms, and the paper's own example

Five specifications are not HumanEval's; they exercise what the HumanEval ones cannot (non-linear invariants, a loop that halves its counter, a library function whose correctness is a theorem to cite, the paper's example).

| Task | What it shows | Derivation (certified) |
|---|---|---|
| `classic_isqrt` | the integer square root `r*r ≤ n < (r+1)*(r+1)` | a loop on `r` with a non-linear invariant, 2 laws |
| `classic_sqrt_approx` | **the paper's example**: given `N ≥ 0` and `e > 0`, return `x` with `x*x ≤ N < (x+e)*(x+e)`. Over `ℚ` rather than the paper's `ℝ`, so that the program can be run on the tests | a loop on a counter `k` with `x = k*e`; the variant is `⌊(N+1)/e⌋₊ + 1 - k`, a natural number; 2 laws and **one helper lemma** (`k+1 ≤ ⌊(N+1)/e⌋₊` from the guard) that Lean proves first |
| `classic_fast_power` | `b^e` by repeated squaring | a loop on `(acc, base, k)` with invariant `acc * base^k = b^e`, a case on the parity of `k`, 4 laws, two helper lemmas (`base^k` for odd and even `k`) |
| `classic_sort_list` | sorted and a permutation of the input | one `term` (`l.mergeSort …`) and one helper lemma that turns the library's `Pairwise` and `Perm` facts into the specification's index form |
| `classic_reverse` | a list reversed | a loop that prepends, with invariant `acc = (l.take i).reverse` |

The square-root derivation is the one to show Dr. Hou: it is the example of the paper (Fig. 2 there, with its loop invariant), here with the termination argument spelled out as a natural-number variant and checked by Lean, instead of the relaxed rule of the Z3 engine (doc 18). The paper's invariant has no `x ≥ 0` conjunct; this one carries `k*e` with `k : ℕ`, so non-negativity is in the type.

## 6. Files

`lean_specs/<id>/{task.json,description.txt,task.lean,test.json}` ×42 (generated; `python benchmarks/datasets/lean_specs.py build` rewrites them), `results/lean_specs/validation.json`, `oracle.json`, `mutation_feedback.json` (doc 22). Tests: `FormalLLM/tests/test_lean_specs.py` (conversions, directory structure, stored validation, lemma proofs, eight oracle derivations re-run).
