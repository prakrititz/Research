# 26 — One interface for Verina and HumanEval (written 2026-10-13)

> Goal: take any command that ran on one dataset and run it on the other by changing one word, `--dataset verina` or `--dataset humaneval`. No model has been run; everything below is measured with the reference solutions and the hand-written derivations.

## 1. What was already the same, and what was not

Both datasets are stored in Verina's directory format (`task.json`, `description.txt`, `task.lean` with `-- !benchmark @start/@end` regions, `test.json`) and both are read by `FormalLLM/lean/task.py::LeanTask` and refined by the same engine. A field-by-field comparison of the 189 Verina and 164 HumanEval task directories (2026-10-13):

| | Verina | HumanEval (ours) | Treatment |
|---|---|---|---|
| files per task | `task.json description.txt task.lean test.json reject_inputs.json` (+ stray `signature.json`, `task-bak.lean`, `coverage_report.md`) | the first four | the extra files are never read |
| `task.json` keys | `id signature specification metadata description_file lean_file test_file reject_inputs_file` | same, no `reject_inputs_file`, plus `input_encoding` | `reject_inputs.json` is unused by any code |
| regions in `task.lean` | `import solution_aux precond_aux precond code_aux code postcond_aux postcond proof_aux proof` (a few add `task_aux`/extra imports) | the same ten | the engine's regexes use `code`, `code_aux`, `proof` only |
| `test.json` entry | `{input, expected, unexpected}` | `{input, expected, unexpected}` | same keys |
| **how an input is written** | JSON values: `5`, `"abc"` is the text `abc`, `","` is the Char `','`, compound values as Lean source (`"#[1, 2]"`) | Lean source for every input (`"[1, 2]"`, `"\"abc\""`) | **`LeanTask.encoding`**: `"json"` / `"lean"`; one method `call_args(case)` |
| how an expected value is written | numbers/bools/strings as JSON, others as Lean source | the same | one function `render(value, type)` (now also handles `Char`) |
| types | `Array Int`, `List Int`, `Nat`, `String`, `Char`, `Float`, `Map` … | `List Int`, `String`, `ℚ`, `Option`, products, sums … | all handled by Lean; the literal writer for *our* generation is separate |
| Lean version | pinned 4.18 (4.24 for `grind`) | 4.34.1 | **`Dataset.compat`**: two renamed constants re-defined (`Array.mkArray`, `Std.HashSet.empty`) |

The first real bug the comparison found: the old Verina harness wrote a String input without quotes (`(aaa)`), which is why only 146 of 189 reference solutions scored; with `encoding="json"` that is fixed for both the evaluator and the engine's `certify`.

## 2. The layers

```
FormalLLM/lean/dataset.py    registry: Dataset(name, root, prefixes, oracle module, input encoding, compat prelude, results dir)
FormalLLM/lean/task.py       LeanTask: reads a directory, writes literals (encoding-aware), builds the #eval test commands
FormalLLM/lean/evaluate.py   score_code (compile + run the tests), validate_task (the four specification checks) — dataset-free
FormalLLM/lean/engine.py     the refinement engine (unchanged by the dataset)
benchmarks/lean_eval.py      one command line: list | validate | reference | compile | goals | automation | oracles | summary
benchmarks/lean_baseline.py  the direct (plain model) baseline: generate | score, --dataset
benchmarks/lean_agent_run.py the refinement agent over many tasks, --dataset
python -m FormalLLM.lean     show | check | oracle | solve   (a task id of any dataset instead of a path)
```

Names: `verina` (189), `humaneval` (164: `he_*`), `classic` (5), `lean_specs` (humaneval + classic). Results go to `benchmarks/results/<dataset>/`. **To add a dataset** (MBPP, ...): put its tasks in the same directory format, add one `Dataset(...)` line to `REGISTRY`; nothing else changes. If its test inputs are JSON values use `input_encoding="json"`.

Old command names still work: `verina_eval.py oracle`, `verina_goal_check.py`, `verina_compile_check.py`, `verina_automation.py`, `verina_baseline.py` are shims for `lean_eval.py` / `lean_baseline.py` with `--dataset verina`. `lean_agent_run.py --library` is an alias of `--dataset`.

## 3. The same checks on both (measured)

`python benchmarks/lean_eval.py validate --dataset D` runs the four specification checks (compiles with its reference solution; the reference passes every test; the postcondition accepts every expected output; it rejects every `unexpected` output). Verina's `test.json` carries `unexpected` lists too, so the numbers are comparable:

| | Verina | HumanEval (ours) |
|---|---|---|
| tasks | 189 | 164 (169 with the classics) |
| compile (reference code, proof replaced by `sorry`) | **180** | 169 / 169 |
| tests | 1,114 | 2,332 |
| reference passes the test | 1,032 / 1,114 (the rest sit in the 24 tasks below) | 2,332 / 2,332 |
| postcondition accepts the expected output | 958 / 1,114 | 2,332 / 2,332 |
| postcondition rejects the wrong output | 2,105 / 2,263 | 5,651 / 5,657 |
| all four checks ok | **165 / 189** | 169 / 169 (one permissive spec) |

The 24 Verina tasks that do not pass all four, by cause (`results/verina/validation.jsonl`):

* **14 have a postcondition Lean cannot run** (`failed to synthesize Decidable (f_postcond ...)`). They are correct Lean, written for proving, with unbounded quantifiers such as `∃ k : Int, n = 11 * k` or `∃ x : Nat, pow 2 x = n`; a quantifier over all integers cannot be decided by running. Our specifications are all written in the decidable shape, so every one of ours can be spot-checked; these 14 can only be judged by a proof. Not a harness problem.
* **9 do not compile on 4.34.1** even with the proof removed. Seven are a `let rec` loop without a termination hint whose automatic termination proof times out on 4.34 (a Lean version change; raising the recursion or heartbeat limits did not help, so it needs a `termination_by` added to Verina's code, which we do not do); `verina_basic_61` uses `String.Iterator.curr`/`next`, whose signature changed; `verina_advanced_68` hits an elaboration-order change (`c.isDigit` with `c`'s type not yet known).
* **1 specification is weak** (`verina_basic_72` accepts 1 of 15 deliberately wrong outputs).

## 4. Derivations on both (hand-written, no model)

`python benchmarks/lean_eval.py oracles --dataset D`:

| | tasks | derivations | certified | tests of the derived programs |
|---|---|---|---|---|
| HumanEval | 164 | **57** (107 problems still have none) | **57 / 57** | all pass |
| classic | 5 | 5 | 5 / 5 | all pass |
| Verina | 189 | 25 | 24 / 25 (`verina_basic_4` needs a witness) | all pass |

All 26 specifications added on 2026-10-11 now have one: **26 of 26 certified** (they are in the 62 above together with the 36 earlier ones). Of the 26: 10 are real loops with an invariant (133, 135, 136, 142, 146, 151, 153, 154, 155, 158), 12 are a `term`/`cases` that restates a decidable specification (134, 137, 141, 143, 144, 145, 148, 149, 159, 161, 163 with a sorting/witness lemma where one is needed), and 4 are *definitional* (140, 156, 160, 162: the specification is a recursive definition and the answer is that definition; 147 is the same with a counting expression). The honest reading: a derivation exists, the four laws reach the task; for the last group nothing was searched.

What the new derivations added to the engine (all kept; 62 / 62 and Verina 24 / 25 still hold):

* lemma library: `getElem_bang_mem`, `getElem_bang_mem_take`, `head_mem_take_one` (an element read at an index is a member);
* the cascade: `(rw [forall_mem_iff_idx]; grind)` and the same for `∃` (a member quantifier whose predicate mentions a loop variable), and helper lemmas are tried on the *whole* goal first (before the goal is split into conjuncts and before `simp_all` expands a literal such as `List.range 10`);
* helper lemmas written for the stability of a sort (`order_by_points`: `List.sublist_mergeSort`), the order of a two-key sort (`sorted_list_sum`), the Option-valued extrema (`largest_smallest_integers`), a witness disjunction (`can_arrange`, `bf`).

## 5. What "blindly replace" means in practice

```
python benchmarks/lean_eval.py reference --dataset verina      # which tasks the harness can score at all
python benchmarks/lean_eval.py reference --dataset humaneval
python benchmarks/lean_baseline.py generate --dataset humaneval --config ornith --rounds 3
python benchmarks/lean_baseline.py score    --dataset humaneval --config ornith
python benchmarks/lean_agent_run.py run --dataset verina --config ornith --tasks verina_basic_5 --repeats 3
python -m FormalLLM.lean oracle he_142_sum_squares --source
```
Each pair differs only in `--dataset`.

## 6. Known differences that remain (and are not hidden)

1. **Test counts**: Verina has 3-10 tests per task (median 5); ours 11-16 (HumanEval's own inputs plus EvalPlus'). A model that passes five tests is checked less strictly on Verina.
2. **Specifications**: Verina's are written by other people for verified synthesis, with proof-carrying indices (`a[i]` with `hi : i < a.size`); ours state a HumanEval problem in decidable shape. A derivation engine tuned on ours can fail on Verina's idioms: 24 / 25 hand derivations say it reads them, not that a model will find them.
3. **Verina's references** are Lean programs for Lean 4.18 (14 + 9 of its tasks do not run as stored, §3); HumanEval's are written by us on 4.34.1.
4. **Floats**: our specifications read Python floats as rationals up to 1e-6 (EvalPlus's tolerance); Verina has two `Float` tasks that are compared with `==`.
5. **The test inputs of our library depend on the EvalPlus data version** (rebuilding the library with `evalplus 0.3.x` here produced different EvalPlus samples for some problems than the stored ones from the Windows laptop). The stored `test.json` files are authoritative; `lean_specs.py build` should not be re-run casually.

## 7. How the derivations were verified (2026-10-13)

1. **Independent recompilation** (`benchmarks/verify_derivations.py`): every finished derivation file is compiled by a plain `lake env lean` in its own process (not the REPL the engine used) and checked from that process's output: no error; `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`; the file contains the dataset's own precondition/postcondition regions as written; every test of `test.json` prints `true`. **Ours 62 / 62; Verina 24 / 24** (the 25th Verina derivation, `verina_basic_4`, is not complete, so there is no file).
2. **Mutation testing of the 26 new derivations** (`benchmarks/lean_mutation_feedback.py --dataset humaneval`): every step was changed once (a number +1, `<` ↔ `≤`, `+` ↔ `-`, a condition...): **152 mutants, 146 rejected (96.1%)**, 85 of them with a counter-example; the 6 survivors are equivalent mutants (the program is still correct, certified and passes its tests): `he_137` second condition after the equal case was excluded; `he_158` replacing the best by an equal string; `he_159` `need = remaining` gives the same result in both branches; `he_136` the initial value of `m` is unused while no element was seen, and the same equal-element case. **No mutant was accepted and failed a test.**
3. **Not verified by either:** that a specification means what the English says (checked against test data only, doc 24), and the four *definitional* derivations (140, 156, 160, 162) say nothing beyond "the specification is itself a definition".
