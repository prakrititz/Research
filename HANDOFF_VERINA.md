# Handoff — 2026-11-12: fix Verina before any paid run

Read [`HANDOFF.md`](HANDOFF.md) first for the setup, the layout and how HumanEval was fixed (§4–§5.3). This file covers
where the benchmark runs stand and what to do for Verina. **Everything is stopped.** No run is active.

**Status 2026-11-12:** §3 is fixed and strict gold on Verina is at **153/177** (it started at 126). §7 has the
progress, §8 the remaining failures, and §9 the probe workflow used to find each fix.

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

## 7. Verina strict gold progress (2026-11-11 to 11-12)

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

HumanEval samples after each change (`run_humaneval_gold_recheck1112{,b,c,d,e}_joint.jsonl`): all solved every time.

All new tactics are in `Derivation._shape_tactics` ([`engine.py`](FormalLLM/lean/engine.py)), each gated on the shape of
the obligation (a word in the statement, the binder types, the obligation kind) and never on a task name. All new
lemmas are `Refine.*` in [`lemmas.py`](FormalLLM/lean/lemmas.py), each with a comment naming the task that first
needed it.

## 8. Remaining Verina failures (24)

None of these is a prover bug; each needs a proof the library does not have yet. Grouped by what is missing:

| family | tasks | what is missing |
|---|---|---|
| the spec is the brute force over subarrays/pairs, the program a `foldl max` over the same set | advanced_30, 38, 42, 71 | the index/`zipIdx` form of the spec against the flatMap of the program; a `foldl max` attained/upper-bound lemma for flatMap of pairs |
| sorted by a key, then `take` | advanced_76 (top-k frequent), basic_104 (map update) | `find?` on a list with unique keys through mergeSort and filter; Pairwise of a sort by key on `zipIdx` |
| `let rec`/recursive task helpers | advanced_1 (`filterlist`), 10 (`removePrimeFactor`, padicValNat), 23 (custom `pow`), 24 (subsequences), 56 (`isSubsequence`), 62 (`ml`/`mr` in the spec) | the helper = a library function, by induction (`fl_eq` style) |
| loop exit with a task-specific fact | advanced_8 (gas station), 52 (min operations), 58 (ugly number), 67 (run-length decode), basic_89 (idxOf dedup), 102 (array two-sum with lex conditions) | per task. advanced_52 is proved by hand in the probe (take of reverse, `k = 0` when the result is 0) but not as a general tactic |
| arithmetic / digits | advanced_5 (add two numbers), basic_43 (Nat subtraction polynomial) | advanced_5 is proved by hand in the probe (task `listToNat` = `Nat.ofDigits 10`, then `Nat.digits_ofDigits`, `Nat.ofDigits_digits`, `Nat.getLast_digit_ne_zero`), not yet general |
| `find?`/second occurrence | advanced_12 (first duplicate), 57 (next greater), 13 (chords), basic_27 (first repeated char) | `idxOf`/`findIdx?` facts |

**Next steps:**
1. The two hand proofs above (advanced_5, 52) show the facts. Turn them into general lemmas only if a second task uses
   the same shape, and otherwise add them as `--lemmas` hand lemmas to the gold tree.
2. The brute-force `foldl max` family (4 tasks) is the largest group, so it is the best next general lemma.
3. Then propose the paid Verina run (§4, step 6). At 153/177 strict gold, the prover ceiling on Verina is
   86%, against 150/159 (94%) on HumanEval.

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
