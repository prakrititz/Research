# Handoff — 2026-11-14: Verina prover at 173/177 strict gold

**Update 2026-11-14 (read §10 first).** The owner chose to keep fixing the prover ("I need the best possible results").
Strict gold on Verina is now **173/177** (155 on 11-13). Two of the 18 new tasks (advanced_58, advanced_67) use tactics
labelled **TASK-SPECIFIC** in `engine.py`; without them the count is **171/177**. Regression samples all pass
(HumanEval 12/12, Verina 8/8, §10).
The gpt-5.4-mini joint failure advanced_11 was a prover gap (fixed; the model's own tree now proves).

## (earlier) Handoff — 2026-11-13: fix Verina before any paid run

Read [`HANDOFF.md`](HANDOFF.md) first for the setup, the layout and how HumanEval was fixed (§4–§5.3). This file covers
where the benchmark runs stand and what to do for Verina. **Everything is stopped.** No run is active and no Lean
process is running. No money has been spent since the $7.31 in §2.

**Status 2026-11-13:**
- Strict gold on Verina: **155/177 (88%)**, up from 126 after the §3 fix. Last commit with a gain: `1af4385`.
- HumanEval strict gold: still **150/159**. A HumanEval sample was re-checked after every change and always passed.
- Target before any paid run: the HumanEval level, about 94%, which is **~166/177**. That leaves **11 to go**.
- **Open decision for the owner (§8):** the 22 remaining failures each need a fact true of one task only. Either accept
  155 as Verina's ceiling (the recommendation), or keep adding task-specific lemmas, labelled as such.

§7 has the progress, §8 the remaining failures and the decision, and §9 the probe workflow used to find each fix.

## 1. Rules from the owner (binding)

- **No paid run until Verina is in a good state.** That means the strict gold run passes on Verina the way it does on
  HumanEval (150/159). The owner is out of credits.
- **A solved task is never re-run.** It stays a success for its configuration, and only failures are re-run.
- Each **configuration** is a branch (L_spec or direct Lean) with one model (joint) or two models (split), and covers
  both datasets.
- **Run order:** one configuration at a time, HumanEval and then Verina, before moving to the next configuration. Never
  start several configurations at once.
- **Gold re-checks run only on the failed tasks.** The one exception is the approved full strict gold run on Verina
  (§4, step 2), which is needed because Verina has never passed strictly.
- The model is **GPT-5.4 mini** (`--model openai:gpt-5.4-mini`) for every configuration.
- **Run at most one Lean process at a time** on a laptop. On a bigger machine you can run more if memory allows; each
  process holds about 3 GB.
- No `Co-Authored-By` or "Generated with Claude" lines in commits.

## 2. Status of each configuration (GPT-5.4 mini)

| # | configuration | HumanEval (159) | Verina (177) |
|---|---|---|---|
| 1 | L_spec, one model (joint) | **done: 147/159** (136 first run + 11 from re-running failures) | **stopped after 1 task** (verina_advanced_1 EXHAUSTED, $0.28), blocked by §3 |
| 2 | L_spec, two models (split) | 1 task so far (he_000 CERTIFIED; its fresh-process file check never ran) | — |
| 3 | direct Lean, one model | not started | — |
| 4 | direct Lean, two models | **not built**: `LeanAgent` only has a one-model mode | — |

- **Baseline (2026-11-11), no refinement:** one prompt per task, one attempt, no feedback. The model writes the Lean
  function body and passes only if it compiles and passes every test, with no proof.
  - **HumanEval: 122/163.** On the 159 L_spec tasks it is 121/159, against 147/159 *verified* for L_spec joint.
  - **Verina: 119/146** (basic 71/83, advanced 48/63).
  - The task sets are the tasks whose reference solution passes every test on our Lean (`lean_eval.py reference`).
  - Results are in `benchmarks/results/{humaneval,verina}/{gen,baseline}_gpt-5.4-mini.jsonl`. Cost $1.00.
  - Command:
    `FORMALLLM_MAX_BUDGET_USD=1.5 python benchmarks/lean_baseline.py generate|score --dataset D --config gpt-5.4-mini --rounds 1`.
- **Cost:** about **$7.31** of the $15 approved: $4.57 joint, $1.42 for re-runs, $0.04 split, $0.28 Verina,
  $1.00 baseline.
- **HumanEval joint failures:**
  - he_009, he_020 and he_090: the model could have solved them, but the prover could not close its loop or case;
  - he_001, 025, 059, 071, 087, 099, 111, 114 and 129: strict gold fails these too, so they are the ceiling.
- **Write-up:** [`benchmarks/results/lspec/failures_gpt-5.4-mini_joint.md`](benchmarks/results/lspec/failures_gpt-5.4-mini_joint.md).
- **Results:** `benchmarks/results/lspec/run_humaneval_openai-gpt-5.4-mini_ex2cross_{joint,fix1110_joint,fix1111_joint,split}.jsonl`.
- **Joint certificates:** the 136 `.lean` files from the joint run were lost. Rebuild them for free by replaying the
  saved trees: `--model gold --trees <results.jsonl>`.

## 3. Bug found: two tactics named `wit_search` (fixed, commit 80a20fe)

**Symptom.** Verina tasks fail with:

> the finished term was not accepted: invalid macro_rules alternative, multiple interpretations for pattern

This happens even on tasks whose gold steps all applied. In the partial strict gold run it hit 10 of 23 tasks:
advanced_15, 16, 17, 18, 19, 21, 22, 25, 26 and 27.

**Cause.**
- `VERINA_COMPAT` ([`FormalLLM/lean/dataset.py:91-104`](FormalLLM/lean/dataset.py#L91-L104)) declares
  `syntax "wit_search"` + `macro_rules`, a small witness search for existential **preconditions**. It is used by
  `task.precondition_proof` ([`task.py:34`](FormalLLM/lean/task.py#L34), [`task.py:222`](FormalLLM/lean/task.py#L222),
  [`evaluate.py:94`](FormalLLM/lean/evaluate.py#L94)).
- The HumanEval prover work (2026-11-09) added a second tactic with the same name: `macro "wit_search"` in the engine's
  library, [`engine.py:214-280`](FormalLLM/lean/engine.py#L214-L280).
- HumanEval has no compat prelude, so it never saw the clash. Every Verina environment holds both definitions.
- Every **proof** failure on Verina so far happened in this broken environment. Any obligation whose cascade reaches
  `wit_search` errors out instead of being tried. So the 13 "goal failed" tasks and the model's verina_advanced_1 run
  are not real evidence yet.

**Fix.** Rename the compat tactic, for example to `pre_wit_search`, in `VERINA_COMPAT` and in the two
`'wit_search' in ...compat` checks plus `precondition_proof`. Alternatively, drop it from the compat prelude and let
`precondition_proof` use the engine's `wit_search`.
- Keep [`retrieval.py:19`](FormalLLM/lean/retrieval.py#L19) (`NOISE`) in line with the new name.
- Then check that Verina tasks with existential preconditions still prove their precondition.
- The obligation cache keys include the task prelude, so changing the prelude invalidates old entries by itself.

## 4. Plan for Verina (as for HumanEval, HANDOFF.md §5.3)

1. **Fix §3.** Run strict gold on the 23 tasks already tried, `--only <those ids>`, to confirm the macro error is gone.
2. **Strict gold on all 177** (approved once):
   ```bash
   python benchmarks/lspec_run.py --dataset verina --model gold --tag v2 --attempts 1 --retractions 0
   ```
   Time: about 2–8 minutes per task here (72–518 s), so many hours on a laptop. Resume-safe: re-running the same command
   skips the rows already written.
3. **For each failure,** run gold with `--lemmas` on just that task. If it passes, the task is blocked only by the
   helper lemmas.
4. **Generalize the missing facts** into [`FormalLLM/lean/lemmas.py`](FormalLLM/lean/lemmas.py) as `Refine.*` lemmas,
   and add them to `NAMES`, plus `SIMP_SET`/`EVAL_SET` for rewrites. Then re-run strict gold **on the failures only**.
   - 97 of 177 Verina gold trees bring hand lemmas (188 in all) and 80 bring none. HumanEval: 49 of 159.
   - The lemma list, grouped by task, is in
     [`benchmarks/results/lspec/verina_hand_lemmas.txt`](benchmarks/results/lspec/verina_hand_lemmas.txt).
   - The families seen:

   | family | tasks (verina_advanced_* unless "basic") | in the library already? |
   |---|---|---|
   | mergeSort is sorted and a permutation (`Pairwise (· ≤ ·)` ∧ `isPerm`) | 16, 17, 48, 49, 50, 51, 81, basic_87, basic_22 | parts: `pairwise_mergeSort_le_int`, `mergeSort_isPerm`, `isPerm_mergeSort`; check the `∧` and `.toArray.toList` forms |
   | `find? p |>.getD d` with count facts: single number, majority, missing number, most frequent | 1, 11, 35, 36, 37, 54, 55 | `find_some_of_any`, `find_majority`, `count_pair_le`; need `filter (· = x)).length = count` |
   | bounded `∃` ⇔ `(range (n+1)).any …`: power of 4, power of 2, a digit 8 | 14, 20, 23 | no; needs a bound lemma (`m < b^m`) |
   | the spec states the brute force: subsequences, subarrays, LIS, LCS | 2, 3, 4, 24, 25, 27, 31–34, 43–46, 74, 75 | short hand proofs (~200 chars); likely unfold + `simp`/`decide` once §3 is fixed |
   | `foldl` arg-min/arg-max by key, `foldl max` | 12, 38, 71, 73, basic_33 | `foldl_max_facts`, `foldl_max_mem_of_mem`, `le_foldl_max`; arg-min by key is new |
   | loop facts (init/step/exit): two-sum, searches, prefix sums, run-length encoding | 8, 52, 53, 58, 67, 78, 79, 80, basic_24, 34, 40, 46, 47, 51, 54, 56, 60, 89, 90, 102, 108 | mostly task-specific; first see what the engine's shape tactics close after §3 |
   | arithmetic identities: sums of powers, div/mod, parity | basic_3, 7, 43, 66, 81 | `omega`/`ring`/`nlinarith`; Nat subtraction in basic_43 |
   | trivial: swap, kth element, filter | basic_4, 64, 91, 92, 93, 96 | should close already; if not, the cause is §3 |
   | task helpers defined with `let rec aux` (e.g. `filterlist`) | 1, 56, 5 | needs the helper = library function (`fl_eq`-style) by induction |

   - Verina gold trees are mostly a single `term` step whose hand lemma is the whole proof. If no general lemma can
     close a task, the alternative is a gold tree with more steps (cases, bind, loop) that the prover can close.
   - The gold tree only shows the task is reachable. The model picks its own steps.
5. **Keep HumanEval at 150.** After any library change, re-run strict gold on a sample of HumanEval tasks whose proofs
   use the changed area. That checks the change broke nothing; it is not a re-run of successes for scoring.
6. **Only then** propose the paid L_spec joint Verina run. Ask the owner first: give the cap and expect about $0.03 per
   easy task and up to $0.25 per exhausted one.
   ```bash
   python benchmarks/lspec_run.py --dataset verina --model openai:gpt-5.4-mini --workflow joint --examples 2 --max-usd <cap> --paid-ok
   ```
   Use the watchdog from the earlier session. It stops the run when more than 70% of tasks fail (n ≥ 10), after
   6 failures in a row, or after 3 errors in a row. It is `benchmarks/watch_run.py <log> <results.jsonl> lspec_run.py`, run in the
   background next to the run. It is Windows-only as written, since it lists processes with PowerShell; on Linux or
   macOS, swap in `pgrep -f`.

## 5. Model-side notes from the one Verina task (verina_advanced_1)

- **Lean-style calls.** The model writes `getD 0` and `getD nums[0]` instead of `getD(0)`. The hint in `steps.py`
  catches it, but each slip costs a call. Consider repairing `x.m a` to `x.m(a)` for a single atomic argument, or a
  cheatsheet line for `getD`.
- **Bind depth.** It hit the 3-bind limit repeatedly (`bind x with count(x) == 1`). The refusal works, but the model
  keeps retrying bind instead of switching to a cases or term step.
- In the gold tree the whole program is one term, `(nums.find? (fun x => nums.count x = 1)).getD 0`. The model found
  that same term, so only the prover failed: missing lemmas, plus §3.

## 6. Files from this session

| file | what |
|---|---|
| `benchmarks/results/lspec/run_verina_gold_v1_joint.jsonl` | partial strict gold, 23 rows, **all invalid because of §3**; delete it after the fix and re-run as v2 |
| `benchmarks/results/lspec/run_verina_gold_strict1111_joint.jsonl` | strict gold on verina_advanced_1 alone: fails (also under §3) |
| `benchmarks/results/lspec/run_verina_openai-gpt-5.4-mini_ex2cross_joint.jsonl` | the model's 1 Verina row (EXHAUSTED); a failure, so it may be re-run after the fixes |
| `benchmarks/results/lspec/verina_hand_lemmas.txt` | the 188 Verina hand lemmas by task |
| `benchmarks/results/lspec/run_humaneval_openai-gpt-5.4-mini_ex2cross_split.jsonl` | split: he_000 CERTIFIED; its file check is still pending |

## 7. Verina strict gold progress (2026-11-11 to 11-13)

Every run is strict gold (`--model gold --attempts 1 --retractions 0`). A task counts only when the fresh-process file
check says SOLVED. Each fix run covers **only the tasks still failing**; HumanEval is checked after every change on a
sample of tasks whose proofs use the changed area.

| run (`run_verina_gold_<tag>_joint.jsonl`) | tasks run | solved | total | what changed |
|---|---|---|---|---|
| v2 | 177 | 126 | 126 | §3 fixed (`pre_wit_search`); counter-example search limited to maxSize 10 and 30 s |
| v2fix1 | 51 | 11 | 137 | max of a list (`maxlist_*`), bounded search `(range (n+1)).any` (`any_range_iff`, `le_pow_self'`), Nat polynomial, Pairwise |
| v2fix2 | 40 | 6 | 143 | flag split (two-sum: `pairsum_exists_of_count`, `ts_*`), arrays as lists, casts and index forms through implications, `sq_window_decide` |
| v2fix3 | 34 | 4 | 147 | `find?`-split: majority (`filter_le_half_or_eq`), missing number (`range_not_subset`, `missing_unique`); array/range quantifiers split at index 0 |
| v2fix4 | 30 | 2 | 149 | most frequent (`not_all_ne_max_dec`, `le_foldl_max`), precondition unfolded by name + index forms + `grind` |
| v2fix5 | 4 | 3 | 152 | index modulo the length (`getD_emod`, `getElem?_emod`), mergeSort result (`array_any_eq_iff_mem`), loop step with a Bool flag |
| v2fix6 | 1 | 1 | 153 | 2-D search: exit with a disjunctive invariant (`all_all_of_bang`), rows of a rectangular array (`rect_row_size`) |
| v2fix7 | 1 | 1 | 154 | maximum of a brute-force list of pairs (`foldl_max_pairs`, `foldl_max_filter_pairs`) with `zipIdx` quantifiers as indices (`pairwise_zipIdx_iff`, `zipIdx_all_iff`, `zipIdx_any_iff`) |
| v2fix8 | 3 | 1 | 155 | the task's recursive helpers recognised as library functions by signature (`Derivation._library_equations`: `pow` = `^`, a digit fold = `Nat.ofDigits`, a `let rec` filter = `List.filter`), then a bounded search for a power (`int_lt_pow`). advanced_1 and 5 get their equation but still need their task-specific rest |

HumanEval samples after each change (`run_humaneval_gold_recheck1112{,b,c,d,e,f,g}_joint.jsonl`): all solved every
time. The last two were 3/3 (he_009, 021, 120, after v2fix7) and 5/5 (he_038, 046, 055, 063, 079, after v2fix8).

All new tactics are in `Derivation._shape_tactics` ([`engine.py`](FormalLLM/lean/engine.py)), each gated on the shape of
the obligation (a word in the statement, the binder types, the obligation kind) and never on a task name. All new
lemmas are `Refine.*` in [`lemmas.py`](FormalLLM/lean/lemmas.py), each with a comment naming the task that first
needed it.

## 8. Remaining Verina failures (22)

None of these is a prover bug; each needs a proof the library does not have yet. Grouped by what is missing:

| family | tasks | what is missing |
|---|---|---|
| the spec is the brute force over subarrays/pairs, the program a `foldl max` over the same set | advanced_30, 38, 71 | the max-of-pairs tactic (v2fix7) gives the facts, but the spec also says the best streak cannot be extended (advanced_30: needs the witness shifted one left), or merges intervals (38), or compares strings by `toLex` (71) |
| sorted by a key, then `take` | advanced_76 (top-k frequent), basic_104 (map update) | `find?` on a list with unique keys through mergeSort and filter; Pairwise of a sort by key on `zipIdx` |
| `let rec`/recursive task helpers | advanced_1 (`filterlist`), 10 (`removePrimeFactor`, padicValNat), 24 (subsequences), 56 (`isSubsequence`), 62 (`ml`/`mr` in the spec) | the helper = a library function, by induction (`fl_eq` style) |
| loop exit with a task-specific fact | advanced_8 (gas station), 52 (min operations), 58 (ugly number), 67 (run-length decode), basic_89 (idxOf dedup), 102 (array two-sum with lex conditions) | per task. advanced_52 is proved by hand in the probe (take of reverse, `k = 0` when the result is 0) but not as a general tactic |
| arithmetic / digits | advanced_5 (add two numbers), basic_43 (Nat subtraction polynomial) | advanced_5 is proved by hand in the probe (task `listToNat` = `Nat.ofDigits 10`, then `Nat.digits_ofDigits`, `Nat.ofDigits_digits`, `Nat.getLast_digit_ne_zero`), not yet general. basic_43's loop step is proved by hand (below); the generic `omega`/`nlinarith` variant fails |
| `find?`/second occurrence | advanced_12 (first duplicate), 57 (next greater), 13 (chords), basic_27 (first repeated char) | `idxOf`/`findIdx?` facts. advanced_57's spec repeats the program per element, but its `match` on `find?` depends on the scrutinee, so `split`/`generalize`/`cases` all fail; needs a rewrite of the match first |

**Hand proofs found in the probe (not in the engine):**
- **basic_43** (loop step): saved in
  [`benchmarks/results/lspec/probe_hand/verina_basic_43__loop_step.lean`](benchmarks/results/lspec/probe_hand/verina_basic_43__loop_step.lean).
  It first proves that the Nat subtractions don't truncate (`12k² ≤ 7 + 24k³` and `14k ≤ 7 + 24k³ − 12k²`, for `k = i`
  and `k = i + 1`), then uses `zify` with those facts and `nlinarith`. Both facts are specific to this polynomial.
- **advanced_52** (loop exit): `take` of a `reverse`, and `k = 0` when the result is 0. The proof file was lost with the
  scratchpad; the facts are listed in the table above.
- **advanced_5**: the digit route in the table above. The equation `listToNat = Nat.ofDigits 10` is now found
  automatically (v2fix8); the rest is not.

**Assessment (2026-11-13).** Every general shape found so far is in the engine. Each of the 22 remaining tasks needs a
fact true of that task only: a specific polynomial never goes below zero, a streak shifted one place left is longer,
a two-step `match` reduces, a recursive helper equals a library function. Getting to ~166 would mean writing about 11
such proofs by hand into the library. That would raise the gold count, but it fits proofs to the test tasks. It
would not help the model run much either, because the model would only succeed if it chose the exact steps each lemma
was written for.

**Decision for the owner (open):**
1. **Accept 155/177 as Verina's ceiling** (recommended). Document the 22 failures with their reasons, as for the
   9 HumanEval ceiling failures (§2).
2. **Keep going with task-specific lemmas.** Label each one in `lemmas.py` as task-specific (not general), and report
   the count with and without them. This would take several more sessions.

**If option 2 is chosen**, the most tractable tasks next are:
- advanced_76 and basic_104 (sort by a key, then `take` or `find?`);
- the loop exits advanced_58 and 67;
- advanced_30 (shift the witness one place left).

The memory rule stands either way: no paid run is proposed until the owner says Verina is fixed.

## 9. Probe workflow (how each fix was found)

1. `python benchmarks/lean_probe.py dump <task ids>` writes each failing obligation as
   `benchmarks/results/lspec/probe/<task>__<obligation>.lean` (the statement with `sorry`).
2. `python benchmarks/lean_probe.py serve DIR` keeps one REPL with the lemma library and each task's definitions
   loaded, and runs every `DIR/<task>__*.lean` that appears, writing `.out` next to it (`OK` or the error). It is one
   Lean process: stop it (`touch DIR/STOP`) before any `lspec_run.py`. It loads `LEMMAS` once, so restart it after
   changing `lemmas.py`, or prepend the new lemmas to the probe file.
3. Write the candidate tactic into a copy of the dumped file (replace `sorry`). Use `done` at the end of each
   `first` alternative: a nested `(by …)` logs its error without failing, so `first` would wrongly accept it.
4. When it says `OK`, write the tactic without task names (use `{post}`, `{pre}`, `‹_›`, binder types) and add it to
   `_shape_tactics` with a gate on the obligation's shape. Then run strict gold on the failures only, and a HumanEval
   sample.


## 10. Prover fixes 2026-11-14 (strict gold 155 -> 172/177)

Runs (`benchmarks/results/lspec/run_verina_gold_<tag>_joint.jsonl`), each on the failing tasks only:

| run | tasks run | solved | total | new tactics (all in `Derivation._shape_tactics`, gated on the obligation's shape) |
|---|---|---|---|---|
| v2fix9 | 10 | 8 | 163 | unique count-1 element (1), argmin fold over a filter match (12), symmetric pair relation vs `Pairwise` (13), longest list via the post's `let rec` generator (24), digits round trip (5), partition by a predicate + library equations for count/subsequence functions (56), non-negative recursive accumulator (62), top-k by key from `eraseDups`+`mergeSort` (76) |
| v2fix10 | 6 | 5 | 168 | brute-force longest streak (30), first-hit search exit and its step (52, 8), next greater element (57), Nat-subtraction polynomial invariant (basic_43) |
| v2fix11 | 5 | 4 | 172 | argmax over indices (38), shortest-then-smallest by `toLex` (71), dedup keeping first occurrences (basic_89), **task-specific**: ugly numbers (58) |
| v2fix12 | 1 | 1 | 173 | **task-specific**: run-length encoding loop step (67) |

Also: the advanced_11 model route (majority named by `bind`, then returned) proves; `with_bound` no longer wraps
multi-line tactics (it broke their layout); `lean_probe.py` prints error line numbers.

**Still failing (4):** advanced_10 (prime exponents: `removePrimeFactor` = `n / p ^ padicValNat`), basic_27 (first
repeated char: `findIdx` on `zipIdx` = the found index), basic_102 (array two-sum with lexicographic conditions),
basic_104 (map update: `find?` on unique keys through `mergeSort`). Each needs a whole-task proof; the gold trees
already carry hand-written proofs for them (`lemmas` in `exports/all_derivations.json`), which strict gold excludes.

**Regression checks:** `run_humaneval_gold_recheck1114_joint.jsonl` (12 HumanEval tasks whose shapes hit the new gates)
and `run_verina_gold_recheck1114_joint.jsonl` (8 previously solved Verina tasks): 12/12 and 8/8.
