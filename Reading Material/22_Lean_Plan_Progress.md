# 22 — Lean-only plan: progress and records (started 2026-10-06)

> Running log of the post-meeting plan (move the pipeline to Lean 4, drop Z3, test on Verina). Newest entry first. Each entry says what was done, the exact command, the result with its denominator, and what it decides. Frozen baseline: stored runs and `replay.py` stay untouched.

## Phase gates (status)

| Phase | Status | Result |
|---|---|---|
| A. HumanEval pilot per problem | **done** | 6 of 20 problems solved at every threshold 20%–100%; mean per-problem verified rate 0.306 |
| 1. Fast Lean (persistent process) | **done (prototype)** | 12.6 s once, then about 0.2 s per obligation (was about 12 s each) |
| 2. Lean against stored obligations | **done: gate passed** | Lean proves 176 of 180 distinct (97.8%); 1,315 of 1,319 weighted (99.7%); median 0.06 s, no timeouts |
| 3. Replace Z3's jobs | **in progress** | counter-examples: small-input search 24%, Lean's `plausible` 29% of Z3's refutations (equality-heavy arithmetic); on the Lean engine's own wrong steps `plausible` alone gives a counter-example for 44% of rejected mutants, running the loop on random inputs raises it to 76%, and the unsolved goal state accompanies every rejection |
| 4. Specs in Lean | **done: all 164 HumanEval problems + 5 classics** | 169 specifications in Lean, validated on 2,332 tests: reference passes 2,332/2,332, postcondition accepts 2,332/2,332 expected outputs, rejects 5,651/5,657 wrong outputs (the 6 are reorderings of one dictionary, `he_111`, whose specification accepts any order on purpose); doc 24 |
| 5. Verina baseline | **in progress** | harness validated on ground truth: 169 of 189 compile, 146 fully scored; model run blocked (server); repo and dataset obtained; 189 tasks confirmed; toolchain mismatch found (Verina: Lean 4.18, ours: 4.34.1); compile check done: 154 of 189 compile on 4.34.1 as shipped, 169 of 189 with proofs ignored |
| 6. Refinement on Verina | **engine built; opens 188 of 189 goals; no model run yet** | Lean-native engine (doc 23): hand-written derivations certified for 36 of 36 library tasks and 24 of 25 Verina tasks (not written by us); model-driven agent built and tested with a scripted model; waiting for a model run |
| 7. Harder families | not started | — |

**Decision (2026-10-11): Z3 is discarded from the pipeline for now.** The base is Lean only, because it is the stronger prover and its kernel is the single trusted judge; accuracy of the outputs comes first, speed second. Z3 may come back later as an optional fast screen (the old code is kept in the tree and in git, untouched; nothing is deleted). What was done to make "Lean only" true rather than nominal:

* `FormalLLM/lean/session.py` no longer imports the Z3-era `FormalLLM/verification` package: it has its own `Toolchain` (elan home, Lake project, REPL path, `short_path`), and `benchmarks/lean_persistent.py` uses it too.
* Checked by blocking the imports `z3`, `lark` and the legacy packages `FormalLLM.{lspec,refinement,verification,lpl,agent,execution}`: the six Lean test files (`test_lean_core`, `_agent`, `_agent_run`, `_dynamic`, `_cli`, `_specs`) pass, 237 of 237 (one stale assertion in `test_lean_core.py` about a `set_option` prefix was fixed on the way). `test_lean_batch.py` tests the old Lean *obligation backend* and still uses the legacy package, so it is outside the Lean pipeline.
* `FormalLLM/requirements-lean.txt` lists what the Lean pipeline needs (`evalplus`, `pytest`); `requirements.txt` (with `z3-solver`, `lark`) belongs to the old engine.
* What Z3 used to do is covered in Lean: step proofs by the tactic cascade (99.7% of all stored obligations), counter-examples by `plausible` and by running the loop (76% of wrong steps), final certification by the kernel and `#print axioms`.

## 2026-10-11 — The Lean specification library now covers all 164 HumanEval problems (no model run)

User instruction: "continue in Lean, for HumanEval for now keep doing that". The snapshot already held 143 specifications (the figure of 42 in the entry below is the state of 2026-10-08; `he_lean/` had grown to problems 0-132 and 138-139, 150, 152, 157 since). Written now: the 26 that were missing, HumanEval **133-137, 140-149, 151, 153-156, 158-163** (`benchmarks/datasets/he_lean/p120_139.py` for 133-137, new `p140_163.py` for the rest).

| | Result |
|---|---|
| Specifications | **169** (164 HumanEval + 5 classic), all compile |
| Tests | 2,332 (HumanEval's inputs that fit the size limits plus a spread of EvalPlus') |
| Reference solution passes | **2,332 / 2,332** |
| Postcondition accepts the expected output | **2,332 / 2,332** |
| Wrong outputs rejected | **5,651 / 5,657**; the 6 are `he_111` (histogram) outputs that are the same dictionary in another order, which its specification accepts on purpose (`permissive`) |
| Not decidable | 0 |

Run: `python benchmarks/datasets/lean_specs.py build --he 133 163`, then `validate --he 133 163` (Lean 4.34.1, Mathlib v4.34.1, 30 s to import Mathlib once). Setup on this machine (macOS arm64; the earlier work was on Windows): `elan` in `~/.formalllm/elan`, a Lake project requiring `mathlib` at tag `v4.34.1` in `~/.formalllm/lean-env-parent/lean-env` (`lake exe cache get`, no compilation), the REPL (`leanprover-community/repl` v4.34.0 with its toolchain set to 4.34.1) in `~/.formalllm/repl`; `python -m pip install evalplus`, and `SSL_CERT_FILE=$(python3 -m certifi)` because the python.org build of Python 3.12 has no system certificates.

How the harder ones are stated (all validated on the data, none by hand):

* **`he_160` `do_algebra`** (operator precedence): a recursive definition `evalOps` that reduces the highest-precedence operator first (the rightmost of the `**`, else the leftmost) with the length of the operator list as fuel. Test inputs are restricted to non-negative operands, no division by zero and no intermediate value above 1e15, so that `//` and `**` agree with Python.
* **`he_162` `string_to_md5`**: MD5 (RFC 1321) written out in Lean on `UInt32` (the 64 constants are `floor(2^32 * |sin(i+1)|)`); the 12 tests include `"Hello world"` and every digest equals Python's `hashlib`. It is a specification by definition; no shorter statement of MD5 exists.
* **`he_156` `int_to_mini_roman`**: greedy decomposition over the table `m cm d cd c xc l xl x ix v iv i`; the reference uses the digit-table form of the canonical solution.
* **`he_145` `order_by_points`**: stability stated without positions: for every weight present, the elements of that weight appear in the same order in the result as in the input, plus equal length and non-decreasing weights.
* **`he_140` `fix_spaces`**: a run of one or two spaces becomes underscores, a longer run one `-`; `fixSpec` with fuel.
* **`he_137` `compare_one`, `he_151` `double_the_difference`**: mixed Python types become sum types (`ℚ ⊕ String`, `Int ⊕ ℚ`): `3.0` is told apart from `3`, which matters because the canonical solution ignores `3.0` (`str(3.0)` has a dot).
* **`he_147` `get_max_triples`**: the specification counts the triples; the reference uses the canonical solution's counting formula.

Three mistakes the validator caught while writing them (all fixed): `he_144` needed its precondition `@[reducible]` so that `native_decide` finds a `Decidable` instance; `he_154` used `List.isInfixOf`, which does not exist in this Lean (`<:+:` and its `Decidable` instance do); `he_156` used a local named `c` and `c[i]!` is Mathlib's *cycle notation* for permutations (`HAppend String (Equiv.Perm ℕ)`).

`FormalLLM/tests/test_lean_specs.py`: 190 passed (its stored-validation test now allows a `permissive` specification to accept a reordered dictionary).

**Not done:** hand-written derivations for the 26 new specifications (`lean_oracle.py` has 36); no model has been run on any of them; the old `validation.json` rows for 0-132 are the ones produced on the Windows laptop (not re-run here).

## 2026-10-08 — The Lean-native core, a 37-problem Lean specification library, and what they measured (no test set run)

User instruction: "maybe not directly run testset but the setup and initial things: more specs, better structure, incorporate Lean". Everything below is infrastructure plus measurements that need no language model.

**1. Counter-examples from Lean itself (`benchmarks/cex_plausible.py`), the Phase 3 question.** Same 794 distinct obligations that Z3 refuted in earlier runs, handed to Lean's `plausible` (this measurement used its default random seed, so repeating it can move each count by a few; the engine itself uses a fixed seed):

| Setting | Counter-example found | Gave up | Error |
|---|---|---|---|
| default instance limit | 165 (20.8%) | 0 | 629 |
| `synthInstance.maxSize 2048` | 204 (25.7%) | 270 | 320 |
| unlimited (`maxSize 100000`, `maxHeartbeats 0`) | **232 (29.2%)** | 540 (68.0%) | 22 (20 are real-valued) |

The 629 errors of the first row were not a property of the statements: Lean's instance search has a size limit (128) that a conjunction of five or more parts exceeds (`Failed to create a testable instance`); a larger limit fixes it. What remains is intrinsic: random generation "gave up after failing to generate values that fulfil the preconditions" for 68%, because these obligations carry equalities such as `q * d + r = n ∧ r ≥ d ∧ r = V0` that sampling cannot satisfy and an SMT solver solves directly; and `plausible` has no sampler for ℝ/ℚ (20 obligations). Median 2.7 s per obligation. Conclusion for old-style arithmetic obligations: no better than the small-grid search (24%). The measurement that matters for the Lean engine is in item 5.

**2. The Lean-native core (`FormalLLM/lean/`, doc 23).** A goal is the subtype `{ρ : T // post ρ}`; four laws (`term`, `cases`, `bind`, `loop`) build a term of it; Lean checks the whole derivation. Obligations are proved by a tactic cascade, a rejection returns the unsolved goal state and a `plausible` counter-example, and a finished derivation is certified by compiling it, requiring no `sorryAx` in `#print axioms`, and running the task's tests. 110 tests for the new core in `FormalLLM/tests/test_lean_*.py` (about 3 minutes with one shared Lean process; the whole project's suite, old and new: 555 passed in 5 minutes).

**3. The Lean specification library (doc 24).** 42 problems in Verina's format: 37 from HumanEval (22 on lists, 8 on strings, 14 scalar; 25 need a loop) and 5 classic algorithms (integer square root, **the paper's square-root approximation over the rationals**, fast power, sorting, reverse). Validation against HumanEval/EvalPlus data and hand-written tests: 551 tests; the reference solution passes **551/551**, the postcondition accepts the expected output **551/551** and rejects **1,201/1,201** mutated wrong outputs. The validator caught one real semantic error (`he_097`: unit digit of the absolute value, not Python's `%`) and a character-encoding bug in the harness.

**4. Hand-written derivations ("oracles") through the engine.** Written without a model; they measure what the four laws and the cascade can do.

| | Derivations | Certified | Tests passed |
|---|---|---|---|
| Our library (`lean_oracle.py`) | 36 | **36** | **475 / 475** |
| Verina's own tasks (`verina_oracle.py`, written by other authors: arrays, `(hi : i < a.size) → a[i]` indices, `Nat` subtraction idioms, a recursive helper in the specification, `List.Pairwise`/`isPerm` sorting specifications) | 25 (20 basic, 5 advanced) | **24** | 134 / 134 of the certified ones |

The first run certified 20 of 25 of ours; the failures were all "bridges" between two ways of writing the same fact (members versus indices, a prefix versus its next element, a guard versus an equality), and they became proved lemmas (`FormalLLM/lean/lemmas.py`) plus a few tactic alternatives. One bridge was a trap: my prefix lemma and a core `simp` lemma undo each other and `simp` looped to the recursion limit (found with `set_option trace.Meta.Tactic.simp.rewrite true`); the core lemma is now removed from the simp set. Tasks whose specification is a recursion `simp` cannot unfold safely (Verina's `sumTo`) or whose solution cites a library theorem (sorting, `Nat.floor`, powers) need a **helper lemma**: a step may carry lemmas that Lean proves first (a false one is rejected); seven derivations use them, among them the paper's square root. The one Verina task not derived (`basic_4`, `arr.any (…)` with an existential witness) needs a witness the cascade cannot guess.

**5. Does the engine catch wrong steps? Mutation testing (`benchmarks/lean_mutation_feedback.py`).** Every oracle step was mutated once (a number +1, `+`→`-`, `<`↔`≤`, `&&`→`||`, `=`→`≠`, in terms, guards, invariants, initial values, results, variants, conditions): **344 mutants, 342 rejected (99.4%)**. The two survivors are equivalent mutants (starting the loop at index 1 instead of 0 where index 0 contributes nothing: the program is still proved correct). **No mutant was accepted and then failed a test (0 of 344).**

The counter-example is the part that changed with the work of the day. First measurement (`plausible` alone, 314 HumanEval mutants): a counter-example for **138 of the 312 rejections (44.2%)**; the rest are invariants whose hypotheses random sampling cannot satisfy (`ok = true ↔ ∀ k < i, …`) and carried the unsolved goal state only. Then `FormalLLM/lean/dynamic.py`: when a loop body is refused, **run the loop** on inputs drawn by `plausible` (the task's inputs, with the precondition as the only hypothesis), starting from `init` and applying the candidate body, checking the invariant, the variant and the postcondition at each iteration. Same 314 mutants: **236 of 312 (75.6%)**; on all 344: 248 of 342 (72.5%). A finding reads, for example (wrong step `≤` where `<` is meant in `below_zero`):

```
counter-example (found by running the loop): operations := [0]
    state (i = 0, bal = 0, neg = false)  invariant true  guard true
      your step gives (i = 1, bal = 0, neg = true)  invariant false  variant 1 -> 0   <- the invariant is false after your step
```

The 94 rejections still without one are loops nested under a `bind` whose property is a hypothesis of the inner loop (`monotonic` 26, `is_sorted` 21, `will_it_fly` 6): there the inner loop's context contains a hypothesis (`up = true ↔ ∀ …`) that random inputs do not satisfy; and `classic_*` (fast power 7, sqrt 9) whose rational/power invariants are not decidable by `decide`. The seed of `plausible` is fixed (`randomSeed := some 20261008`), so the same wrong step gets the same counter-example in every run. Time 885 s for all 344 including counter-example search.

**6. Can the engine open Verina's goals? (`benchmarks/verina_goal_check.py`, no model.)** For all 189 tasks: read the task, load the lemma library and the task's own definitions (precondition, postcondition, helper definitions, without the reference code and proof) into Lean 4.34.1, open the root goal. **188 of 189 load: 108/108 basic, 80/81 advanced** (110 of the 188 have the trivial precondition `True`). The one failure, `verina_advanced_68`, is the task's own specification not elaborating under 4.34.1 (`c.isDigit` with `c`'s type not yet known, a change of elaboration order since the 4.18 that Verina pins); it is a dataset-version problem, not the engine's. So Phase 6 is not blocked by loading: what remains is a model that proposes the derivations. Time 124 s including the 80-s import of Mathlib.

**What this decides.** (1) Lean can be the only prover for the Verina style: no Z3 was used anywhere in items 2–5. (2) The feedback that matters is the unsolved goal state plus, for loops, a run of the loop: `plausible` on a single step is weak where the step's hypotheses are an invariant (44%), running the loop on the task's inputs is strong (76%). That is the answer to "what replaces Z3's counterexamples": not a solver, but execution. (3) For the professor: **no derivation the engine accepted failed a test**: 0 of the 344 mutants and 0 of the 60 correct derivations; the 2 accepted mutants are provably equivalent. The guarantee comes from the Lean kernel checking the finished term, not from a heuristic.

**Not done, deliberately.** No model was run (the user asked for set-up, not test sets; the hosted endpoint is still down). The Verina baseline (`verina_baseline.py generate/score`) is untouched and not started.

## 2026-10-07 — Two findings: the automation floor, and local models make the baseline possible

**1. Automation floor (`benchmarks/verina_automation.py`, no model):** with the GROUND-TRUTH code given, a fixed cascade (`unfold; simp_all | grind | omega | aesop | decide`, heartbeat-limited) proves the postcondition for **37 of 189 tasks (19.6%; 37 of the 169 that compile = 21.9%)**: 34 `basic` and 3 `advanced`. For comparison, Verina reports 3.6% proof success for its best model. So a derivation must contribute on at least 80% of tasks, mostly advanced ones, where plain automation almost never works (3 of 81). This is the room refinement has: it builds the proof in pieces automation can close.

**2. The hosted model is still unreachable (HTTP 403), but local models exist.** Ollama on this laptop holds `qwen3.5` (6.6 GB), `ornith:9b` (5.6 GB), `llama3.1` (4.9 GB) and `qwen3.8` (17 GB), and the RTX 5060 (8 GB) runs the first three on the GPU. Earlier studies (Study 1) found these local models fail the harder refinement tiers, which is exactly the regime where refinement should help, so a weaker model is the better test of the paper's claim.

**3. Verina plain-model baseline built (`benchmarks/verina_baseline.py`):** the model sees the Lean file with the function body as `sorry` plus the description and one example, and writes the body; scoring is compile plus every test case, on the **146 tasks whose ground truth passes in our harness**, with several rounds per task (per-problem rule). Two harness mistakes found and fixed on the way: the refinement provider forces a JSON reply, which made small models invent their own JSON schema (now free text); and models sometimes repeat the whole `def` (now the body is extracted). First sample (ornith:9b, 8 advanced tasks, 1 round): 4 solved, 4 compile errors.

**Run interrupted by the system's low-memory guard (2026-10-07 02:24), not restarted.** Cause measured: Ollama's `llama-server` holds **7.3 GB** of RAM and the Lean-with-Mathlib process another **3.2 GB**; free memory fell to about 1 GB. Partial results kept in `baseline_ornith_v0_partial_killed.jsonl`: 32 attempts on 11 tasks, of which **12 solved (37.5%)**, 17 failed to compile (`failed to synthesize instance`, type mismatches, a repeated `def` header or an `@[...]` attribute that the first extractor mishandled), the rest compiled but failed tests. About a third of generations ran to the 2,048-token cap (about 48 s) by explaining instead of coding.

**Fixes made so nothing else changes between runs:** (1) the baseline now runs in **two phases**, `generate` (model only) then `score` (Lean only), so the two memory-heavy processes never coexist; (2) helper definitions the model writes before the main `def` go into Verina's `code_aux` region (Verina allows them) and a repeated signature is stripped (`split_reply`, checked on five reply shapes). Commands: `python benchmarks/verina_baseline.py generate --config ornith --rounds 3`, then `... score --config ornith`.

## 2026-10-07 — Verina harness fixed: 146 of 189 tasks fully scored on the ground truth

**Cause of the 83 failures found:** not the preconditions (most are `True`), but how I rendered expected values. `test.json` stores a non-`String` expected value as a Lean literal string (`"some 2"`, `"#[1, 2, 5, 6]"`); I quoted it, so Lean reported "String is not Option Int". Fixed in `verina_eval.py` (use the literal as written unless the return type is `String`).

**Re-run (all 189 tasks, ground-truth code):**

| | Tasks |
|---|---|
| Compile (proof set to sorry) | 169 |
| Compile and pass **every** test case | **146** |
| Compile, one test case fails | 1 |
| Compile, all cases error | 22 (23 with an unprovable-precondition error in total: non-trivial preconditions such as `n > 0 /\ primes.all Nat.Prime`) |
| Do not compile on 4.34.1 | 20 |

**So the harness now scores 146 of 189 tasks (77%) as is**, which is enough to start a baseline. The remaining 23 need their preconditions proved per task. Server check at 2026-10-07: the tunnel still answers HTTP 403, so no model baseline yet.

## 2026-10-06 — Phase 3, first job: counterexamples by testing (result: weaker than Z3)

**Question:** if Lean replaces Z3, can the existing evaluator search small inputs and recover the counterexample the refiner feeds back to the model?

**Method** (`benchmarks/cex_by_testing.py`): replay 12 stored runs rich in rejected steps (division, no-assist, strict), record every obligation Z3 refuted, run a small-input enumeration (integers -3..10, reals from a 10-value set, up to 40,000 tries, variables defined by an assumption's equation computed rather than enumerated).

| | Count |
|---|---|
| Z3 refutations seen | 1,206 (794 distinct) |
| Found by small-input search | **188 of 794 (24%)** |
| Not found, but assumptions evaluate fine | the large majority: the real counterexamples lie outside the small grid |
| Not searchable (arrays) | 0 in this sample |
| Median search time | 0.002 to 0.15 s |

On the division runs alone the hit rate is 58% (87 of 150 sampled). Diagnosis: the failing assumption sets are mostly equalities plus bounds over four or five variables, so independent small grids rarely hit a violating state, while Z3 solves for one directly.

**Decision input:** feedback to the model would get much weaker if testing replaced Z3. The plan's fallback applies: keep Z3 as the counterexample provider (and fast screen) and use Lean as the step prover and final judge, unless a smarter search (random sampling over wider ranges, solving linear equalities) lifts the rate; that is a bounded follow-up, not tried yet. No change was made to the engine.

## 2026-10-06 — Phase 5, step 3: Verina harness validated on the ground truth

**Run:** `python benchmarks/verina_eval.py oracle` (all 189 tasks, ground-truth code, memory freed by the user; full Mathlib in one process).

| | Tasks |
|---|---|
| Compile on Lean 4.34.1 (proof set to sorry) | 169 |
| Compile and pass **every** test case | **86** |
| Compile, but every test case errors | 83 |
| Do not compile (`Array.mkArray` 9, `simp` in code 7, `Std.HashSet.empty` 2, other) | 20 |

The 83 are a harness limit, not a problem with the tasks: the generic tactic used to prove each task's *precondition* when calling the function (`trivial | simp | decide | omega`) cannot discharge non-trivial preconditions, so every call is rejected. So the harness can score **86 of 189 tasks as is**; the 83 need preconditions proved per task (for example by `decide` on concrete inputs after unfolding, or by passing the precondition through a `by simp_all`), which is the next fix.

## 2026-10-06 — Phase 5, step 2: evaluator built; oracle run interrupted (memory)

**Built:** `benchmarks/verina_eval.py`: a candidate replaces the code region of `task.lean` (proof set to `sorry`), is compiled in the persistent Lean process, and each `test.json` case is run as `#eval (f inputs proof == expected)`. A first bug made every test count as failed (Lean reports `#eval` output with severity `info`, not `information`); fixed after reading one raw reply, which showed `true` for the three cases tried on `verina_basic_15`.

**Not yet measured:** the oracle run (ground-truth code on all 189 tasks, to learn how many tasks the harness can score at all) was stopped by the system's low-memory guard (about 2.6 GB free; importing all of Mathlib is the heavy part). Not restarted automatically. A lighter way is to import only the Mathlib modules a task needs, or to run when memory is free.

**Model baseline:** blocked, the hosted model's tunnel is still returning the ngrok bandwidth-limit page (checked 2026-10-06 19:50).

## 2026-10-06 — Phase 2: Lean against every stored obligation (gate passed)

**Collect** (`python benchmarks/lean_audit_collect.py`, about 40 minutes, offline): each of the 613 stored successful v8-code runs was replayed from its stored model replies and its final derivation's obligations re-derived exactly as the certifier does. 612 replays reproduced; one did not (Z3 luck on a hard step, the same effect as in `14` §5f). **1,319 obligations, 180 distinct** (137 assignment, 30 loop, 11 skip, 1 weaken-pre, 1 iteration); the highest repeat count of one obligation is 85. The earlier figure of 2,204 could not be reproduced; the true count is 1,319 (1,322 when summed from certificates).

**Run** (`python benchmarks/lean_audit_run.py --timeout 60`, persistent Lean, small Mathlib imports): every distinct obligation, with a kill-and-restart on timeout.

| | Distinct (180) | Weighted by repeats (1,319) |
|---|---|---|
| Lean PROVED | **176 (97.8%)** | **1,315 (99.7%)** |
| Lean UNKNOWN | 4 | 4 |
| Timeouts / restarts | 0 | — |

Median check 0.06 s. **The plan's proposed gate (95% or more) is met.**

**Against Coq on the same obligations:** Coq's recorded failures cover 12 distinct obligations; Lean proves 9 of those 12. So Lean is both faster and stronger than Coq here.

**The 4 Lean did not prove** (all `assignment`; each is `grind failed`, not a refutation):
1. and 2. integer division: after `q := n / d` (floor division), `n - q*d` lies in `[0, d)`; needs a division lemma that none of the cascade's tactics supplies (Coq also fails on both).
3. a `gcd` goal whose truth needs reasoning about divisibility (`d > a` cannot divide `a`), under a quantifier.
4. an excluded-middle tautology over a long existential; the cascade has `omega`, `linarith`, `nlinarith`, `positivity`, `grind`, but not `tauto` or a case split on the existential.
A quick attempt with `tauto` and guessed lemma names did not close them (names such as `Int.fdiv_add_fmod` do not exist in this Mathlib); finding the right lemmas is a small follow-up, not a blocker.

**Reading it:** replacing Z3 as the step-by-step *proof* engine looks feasible on everything the system has ever derived. The open parts are the other three jobs (counterexamples, the leaf helper's screening, feasibility) in Phase 3.

## 2026-10-06 — Phase 5, step 1: Verina obtained and inspected

**Obtained:** `git clone https://github.com/sunblaze-ucb/verina` into `~/.formalllm/verina` (GitHub and Hugging Face are reachable from the laptop).

**Verified against the plan's claims (read from the files, not from the paper):**
- **189 tasks** confirmed: 108 `verina_basic` and 81 `verina_advanced`. Each folder has `task.json` (signature, description, upstream source), `description.txt`, `task.lean` (ground-truth code, precondition, postcondition and proof, with `!benchmark` markers) and `test.json` / `reject_inputs.json`.
- Specs are plain Lean over `Array Int`, `List`, `String` and so on, for example `(exists i, i < a.size - 1 /\ a[i]! + 1 = a[i + 1]!) <-> result`. The engine's own spec language cannot state these (no strings, no list results), so reading Lean specs is the first real engineering step, as the plan says.
- Verina's own protocol already runs several **rounds** per task (`rounds = 5` in the example config) and has tasks for code, specification, proof and their combinations, which matches the per-problem rule described at the meeting.
- **Toolchain mismatch (new):** Verina pins **Lean 4.18.0** (optionally 4.24.0 for `grind`); this laptop has **4.34.1** with a Mathlib built for it. Whether Verina's files compile here is being measured.
- Only **46 of 189** tasks ship a manual proof (as the paper says); the others may carry placeholder proofs (`sorry`), which the first check reports separately.

**Measured:** full `import Mathlib` in the persistent process takes **111 s once** (against about 12 s for the four small modules the obligations use), then each task check takes 0.1 to 1 s.

**Result of the compile check (189 task files, Lean 4.34.1, one persistent process, median 0.16 s per task):**

| Status | Tasks | Meaning |
|---|---|---|
| CLEAN | 31 | compiles, ground-truth proof included |
| SORRY | 123 | compiles; the proof is a placeholder (most tasks have none) |
| ERROR | 35 | does not compile on 4.34.1 |

So **154 of 189 (81%)** can be read by our toolchain unchanged. The 35 errors are version drift, not hard problems: 9 use `Array.mkArray` (renamed since 4.18), 2 use `Std.HashSet.empty`, and about 15 are proofs whose `simp` or `rewrite` steps no longer fire. Only the proofs matter for those; a refinement run needs the code, precondition and postcondition, so many of the 35 may still be usable once their proofs are ignored (to be checked). The alternative, a second Lean 4.18 installation, is not needed for now.

**With every proof replaced by `sorry`** (`--no-proof`, i.e. only the code, precondition and postcondition must compile, which is all a refinement run needs): **169 of 189 (89%) compile**; 20 do not: 9 use `Array.mkArray`, 7 have a `simp` failure in code or helper definitions, 2 use `Std.HashSet.empty`, 2 other API changes. The 20 are `verina_advanced_{2,3,4,25,44,68}` and `verina_basic_{20,23,27,52,57,61,64,74,75,79,83,86,105,106}`. They need a few renamed constants rather than a second Lean installation. Files: `benchmarks/results/verina/compile_check.jsonl` and `compile_check_noproof.jsonl`.

**Superseded line:** the compile check was started with `python benchmarks/verina_compile_check.py` over all 189 task files (results in `benchmarks/results/verina/compile_check.jsonl`; statuses CLEAN = compiles with a proof, SORRY = compiles with a placeholder proof, ERROR = does not compile on 4.34.1).

## 2026-10-06 — Phase 1: a persistent Lean process (the Lean REPL)

**Setup:** cloned `leanprover-community/repl` tag v4.34.0 into `~/.formalllm/repl`, set its toolchain to the installed Lean 4.34.1, `lake build` (24 jobs, succeeded). Wrapper: `benchmarks/lean_persistent.py` (`PersistentLean`: import Mathlib once, then `check(theorem)` against the kept environment).

**Baseline measured first:** one obligation through the existing path (`lake env lean file.lean`): 23.3 s cold, then 11.9 s twice (warm), with a background job also using the CPU.

**Result:** Mathlib import 12.6 s once; then 6 stored obligations in 1.3 s total (0.22 s each; range 0.05 to 0.57 s). That is about 50 times faster per obligation, and under the 1 s target set in the plan (proposed gate: typical obligation under about 1 s) **met**.

**Soundness check of the prototype** (so speed is not bought with wrong answers): a true theorem is `PROVED`; a false one fails with "`grind` failed"; a theorem containing `sorry` is rejected ("declaration uses sorry"); and the session still proves a true theorem afterwards (0.02 s).

**Not yet tested:** timeouts for a hard obligation (a runaway tactic would block the one shared process; needs a per-check timeout and restart); unsupported obligations; memory growth over thousands of checks. Also found installed: `plausible`, Lean's random-testing library, to evaluate for Phase 3 counterexamples.

## 2026-10-06 — Phase A: per-problem scoring from stored runs

**Command:** `python benchmarks/pilot_per_problem.py` (reads `he_refine_v8.jsonl`, `he_refine_v8_heldout.jsonl`, `he_refine_v7.jsonl`, all v8 code; runs lost to the network or the outage excluded; writes `benchmarks/results/datasets/pilot_per_problem.md`).

**Rule used:** a run is *verified* if the derivation completed, every original and EvalPlus test passes, and Coq certified every obligation. A problem is solved at threshold t if its verified fraction of valid runs is at least t. The professor's actual number of tries and threshold are unknown (question to ask).

**Result (121 valid runs, 20 problems):**

| Threshold | Problems solved of 20 |
|---|---|
| 20%, 40%, 50%, 60%, 80%, 100% | **6** (the same six at every threshold) |

The six are `car_race_collision`, `triangle_area`, `add`, `is_equal_to_sum_even`, `right_angle_triangle` (all runs verified) and `sum_to_n` (6 of 6). `multiply` is verified in 1 of 8 runs (12.5%), so it enters only at a threshold of 12.5% or lower. Mean per-problem verified rate 0.306; pooled 41 of 121 runs, consistent with the earlier run-level count.

**Reading it:** the per-problem view does not change the story, because each problem is solved every time or almost never; the choice of threshold only matters between 1% and 12.5% (multiply) and is otherwise flat. 6 of 20 problems is 30%, against the 7 of 20 reported earlier, which counted any single verified run.

## 2026-10-06 — Obligation count for Phase 2

**Question:** how many obligations exist in the stored successful runs (the meeting notes said 2,204)?

**Method:** sum the `obligations` field of every stored certificate in successful, valid v8-code runs.

| Source | Successful runs | Obligations | Coq-certified |
|---|---|---|---|
| Square root (3 files) | 120 | 360 | 360 |
| 12-case batch, run 1 | 220 | 432 | 432 |
| 12-case batch, run 2 | 220 | 432 | 430 |
| HumanEval pilot | 53 | 98 | 85 |
| **Total** | **613** | **1,322** | **1,307** |

**Finding:** 1,322, not 2,204 (I cannot reproduce the earlier figure). Most are repeats of the same derivation across trials, so Phase 2 should audit the *distinct* obligations, which will be far fewer; counting those is the next step.
