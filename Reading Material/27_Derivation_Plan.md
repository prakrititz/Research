# 27 — Derivations for every HumanEval and Verina task (written 2026-10-14)

> Question: "are the derivations written for all HumanEval problems, and for Verina?" Answer at the time of asking: no — 57 of 164 HumanEval problems and 24 of 189 Verina tasks had one. This note records what was done to change that, what each derivation *is*, what is still missing and why, and how to check it. No model was run; every derivation below is hand-written Lean/refinement-calculus JSON, certified by the engine and re-compiled in a fresh Lean process.

## 1. Where things stand

| | tasks | with a derivation | certified by the engine | blocked by the Lean version | not derived (reason in §5) |
|---|---|---|---|---|---|
| HumanEval (Lean specs, `he_*`) | 164 | **159** | 159 | 0 | 5 |
| the five classics (`classic_*`) | 5 | **5** | 5 | 0 | 0 |
| Verina basic | 108 | see below | | | |
| Verina advanced | 81 | see below | | | |
| **Verina total** | 189 | **174** (+4 in progress, see §5) | 174 | 9 | 6 |

"Certified" means: the whole refinement term type-checks in Lean 4.34.1 (loop termination proofs included), `#print axioms <f>_spec_satisfied` lists only `propext`, `Classical.choice`, `Quot.sound`, and the program passes every test of the task. The numbers are produced by `python benchmarks/lean_eval.py oracles --dataset <d>`; the independent re-check is `benchmarks/verify_derivations.py` (§6).

## 2. What a derivation is, and the three labels

A derivation is a tree of the five laws of `FormalLLM/lean/laws.py` (`term`, `cases`, `bind`, `loop`, plus the helper lemmas attached to a step). The engine turns every step into proof obligations, proves them with one tactic cascade (`make_cascade`), assembles the finished Lean file and has Lean check it. The labels (computed by `benchmarks/export_dataset.py::kind_of`):

* **loop** — the tree contains an invariant-based loop. The algorithmic content is in the invariant, guard and variant. HumanEval 87 + classics 4, Verina 63. Examples: the integer square root, the two-sum search (nested loops), staircase search in a matrix, `SetToSeq` (first occurrences in order).
* **restate** — no loop. One or a few `term`/`cases`/`bind` steps whose helper lemmas do the work. This covers (a) declarative checks (the postcondition is already a decidable test; the term is that test), (b) *brute-force restatements*: the specification enumerates a search space ("all subsequences", "all subarrays", "all pairs") and asks for a member that is at least every other; the derivation is `foldl max` over the same enumeration plus a generic lemma ("the maximum of a non-empty list is a member and an upper bound"). These are honest but not clever: the programs are exponential on purpose (they are what the specification literally says), run fast enough on the tests, and say nothing about an efficient algorithm. HumanEval 69, classics 1, Verina 111.
* **definitional** — the specification is itself a recursive definition and the answer is that definition (HumanEval 3).

The label says what the derivation contains, not how hard the task is: a `restate` for the longest increasing run (Verina advanced 30) needs a 60-line proof about windows, while a `loop` for a closed-form sum is five lines.

## 3. The families and the lemma toolkit

The Verina tasks fell into a small number of shapes; each has a template that is reused and a generic lemma that carries the proof. All lemmas live in `FormalLLM/lean/lemmas.py` (namespace `Refine`) or in the `with_lemmas` list of the task; Lean proves each before it is used.

| family | tasks (examples) | template | generic lemmas |
|---|---|---|---|
| scan with an accumulator | sums, counts, min/max, "all/any" checks | `loop` over an index, invariant over the prefix | `forall_mem_iff_idx`, `exists_mem_iff_idx`, `take_succ_bang`, `filter_take_succ_bang` |
| builder | map/reverse/filter/copy into a new array | `loop` with `acc.push`, invariant `acc[j] = f j` | `getElem_bang_*` |
| search (first/last hit) | `lastPosition`, `BinarySearch`, `canCompleteCircuit`, `minimumRightShifts` | `loop` with "nothing before the index matches", exit lemma | `sorted_arr_le`, `arr_all_take_iff`, `arr_all_drop_iff` |
| max/min over an enumeration | LIS (7 tasks), LCS (3), subarray sums (5), best pair, strength | `term (foldl max …)` | `foldl_max_facts`, `maxlist_nat`, `maxlist_int`, `maxlen_spec`, `longest_spec`, `fold_minkey`, `argmin_facts`, `allsub_nil_mem` |
| majority / unique element | `majorityElement` ×3, `findMajorityElement`, `FindSingleNumber` | `find?` + uniqueness from counting | `count_pair_le`, `filter_pair_le`, `find_majority`, `find_some_of_any` |
| two-sum searches | `twoSum` ×4 | outer loop, `bind` inner loop, lexicographic-first invariant | `ts_inner_step`, `ts_inner_exit`, `ts_outer_step`, `ts_lex_all`, `ts_pairwise_none` |
| sorting / permutation | `mergeSorted`, `sort`, `topKFrequent` | `mergeSort` + `pairwise_mergeSort` | `List.mergeSort_perm`, `nodup_eraseDups` |
| digits / arithmetic | `addTwoNumbers`, power of 2/4, digit 8 | `Nat.digits`, bounded `any` | `Nat.ofDigits_digits`, `Nat.lt_pow_self` |
| association lists | `update_map` | filter + append + `mergeSort` | `find_key` |

New library lemmas this round (all proved by Lean): `forall_mem_drop_iff`, `exists_mem_drop_iff`, `forall_mem_take_iff`, `arr_all_take_iff`, `arr_all_drop_iff`, `sorted_arr_le`, `foldl_max_facts`, `maxlist_nat`, `maxlist_int`, `maxlist_int_any`, `maxlen_spec`, `longest_facts`, `longest_spec`, `allsub_nil_mem`, `allsub_nil_mem_arr`, `allsub_rev_nil_mem`, `filter_pair_le`, `count_pair_le`, `find_some_of_any`, `find_majority`, and the six `ts_*` lemmas.

## 4. Changes to the engine and the harness that the derivations forced

1. **Tasks without a precondition argument.** Three Verina tasks (`verina_basic_48`, `verina_advanced_44`, `verina_advanced_74`) state the theorem without `h_precond`: the function and `_postcond` take no proof, so the statement is claimed for every input. `LeanTask.precond_arg` (detected from `task.lean`) makes the engine's root goal, the generated function and the test calls omit it; nothing is weakened.
2. **Existential preconditions.** A precondition like `∃ i j, i < s.size ∧ …` is not decidable, so the test harness could not build the proof argument of `#eval f (#[…]) (proof)` and every test "did not run" (this made 6 reference solutions fail the validation). The Verina prelude now defines a tiny tactic `wit_search` (try the witnesses 0…5 for every `∃`), appended to the harness's proof alternatives. The prelude is also used when `certify` runs the tests.
3. **Helper lemmas first.** The cascade tries a task-local helper lemma on the whole goal before anything else (done earlier, kept); the new `ts_*` wrappers rely on it.
4. **`Dataset.compat` in `certify`.** The dataset's prelude is now put in front of the test run.

## 5. Not derived — and why (stated, not hidden)

| task | reason |
|---|---|
| `he_015_string_sequence`, `he_019_sort_numbers`, `he_086_anti_shuffle` | the specification is about `String.splitOn`; Lean 4.34 has no lemma relating it to list operations |
| `he_032_find_zero` | needs a root bound and a Lipschitz bound for polynomials over ℚ (bisection); not attempted |
| `he_039_prime_fib` | the specification is unsatisfiable for n > 14 and the kernel cannot decide the primality of 28-digit Fibonacci numbers |
| `verina_basic_23, 52, 57, 74, 75, 79, 86` | the reference code does not compile on Lean 4.34.1 (the automatic termination proof of a `let rec` times out); decision: listed, not patched |
| `verina_basic_61` | reference code uses `String.Iterator.curr/next` whose signature changed after Lean 4.18 |
| `verina_advanced_68` | the specification does not elaborate on 4.34.1 (`c.isDigit` with `c`'s type not yet known) |
| `verina_basic_25`, `verina_basic_63` | the postcondition is a `Float` equality; `Float` operations are opaque and the dataset's own `axiom`s are needed to prove `x == x`. The certificate refuses declared axioms, so these cannot be certified without weakening it |
| `verina_advanced_10` (`findExponents`) | needs the factorisation theory of `padicValNat` against the task's well-founded `removePrimeFactor`; a plan exists (§7), not yet closed |
| `verina_advanced_47` (`mergeIntervals`) | needs the sort-and-merge invariant for four conjuncts including "no spurious merge"; not closed |
| `verina_advanced_58` (`nthUglyNumber`) | needs a bound for the n-th ugly number (powers of two) before the search loop terminates; not closed |
| `verina_advanced_67` (`runLengthEncode`) | needs a decode-after-append lemma and a stack-order invariant; not closed |

(The four `verina_advanced_*` rows are the only tasks that are reachable in principle and not done; if a later pass closes them this table shrinks.)

## 6. How the derivations were checked

1. **Engine certificate** (every task): compile + three standard axioms + tests. Full regression on 2026-10-13/14: HumanEval + classics 164/164, Verina 173/174 (the 174th, `verina_basic_4`, was an incomplete first-batch derivation: its witness lemma was added afterwards and it certifies alone; it is part of the re-run below).
2. **Independent recompile** (`benchmarks/verify_derivations.py --dataset verina|lean_specs`): the finished file is written to disk and compiled by `lake env lean` in its own process; no error, only the three standard axioms, the file contains the dataset's own precondition/postcondition regions verbatim, and every test prints `true`. Output: `benchmarks/results/<dataset>/verification_<dataset>.json` and `verified/<task>.lean`.
3. **Mutation tests** (`benchmarks/lean_mutation_feedback.py --dataset …`): the derivation's program is mutated and the tests must notice. See `22_Lean_Plan_Progress.md` for the numbers.

## 7. Plans for the four open tasks (so the next session need not rediscover them)

* `findExponents`: `result := primes.map (fun p => (p, padicValNat p n))`. Lemma R: `removePrimeFactor m p = m / p ^ padicValNat p m` for prime `p`, `m > 0` (strong induction, `padicValNat.mul`, `padicValNat_self`). Then by induction on `primes` (nodup, prime): `n = p^e * (n / p^e)` and `padicValNat q (n / p^e) = padicValNat q n` for `q ≠ p`.
* `mergeIntervals`: sort by start, fold with the running interval; invariants: result sorted and strictly separated, every input covered, bounds come from input endpoints, nothing merged without a witness chain.
* `nthUglyNumber`: search loop with variant `2^n - x`; lemma `isUgly (2^k)` by induction on `divideOut`, hence at least `n` uglies below `2^n`.
* `runLengthEncode`: accumulate runs in a stack; `decodeRLE (xs ++ ys) = decodeRLE xs ++ decodeRLE ys`; `replicate_succ'` for the extension step.

## 8. Where to look

* `exports/` — a readable copy of all specifications and derivations (regenerate with `python benchmarks/export_dataset.py`; its `README.md` explains the files).
* `benchmarks/datasets/lean_oracle.py`, `lean_oracle_he_a.py`, `lean_oracle_he_b.py` — HumanEval and classics derivations.
* `benchmarks/datasets/verina_oracle.py` and `verina_oracle_b.py … verina_oracle_ab.py` — Verina derivations (one module per batch; `derivation_dsl.py` has the five constructors).
