# Failure analysis: GPT-5.4 mini, L_spec joint, HumanEval (159 tasks)

Results file: `run_humaneval_openai-gpt-5.4-mini_ex2cross_joint.jsonl` (this folder). Every number below is computed from
that file, except where another source is named. The run took place 2026-11-09 to 2026-11-10.

## 1. Setup

| Setting | Value |
|---|---|
| Agent | `LSpecAgent`, workflow `joint`: one call writes one refinement step in L_spec |
| Model | `openai:gpt-5.4-mini`, temperature 0.2, 1 sample per attempt |
| Protocol | strict (Refine4LLM's): the model never writes proofs; the prover proves every obligation |
| Limits per task | 30 model calls, 4 refusals per goal, 3 retractions, at most 3 nested `bind` steps |
| Prompt | the joint prompt, the L_spec cheatsheet, and 2 worked examples from the other benchmark (`--examples 2`, pool `cross`) |
| Repair | on (`repair.py`) |
| Verification | each certificate is compiled again in a fresh Lean process after the run (`--file-check end`) |
| Cost | $4.57 |
| Wall time | about 21 h of model-phase time. The PC slept from 01:04 to 13:07 on 2026-11-10; this paused the run without changing any result. |

## 2. Headline

| | Tasks |
|---|---|
| **Solved and verified in a fresh process** | **136 / 159 (85.5%)** |
| Exhausted (out of attempts or calls) | 22 |
| Certified in the session but failed the fresh-process check | 1 (he_069) |
| Reference (gold) derivations under the same strict prover | 150 / 159 (`run_humaneval_gold_v3_joint.jsonl`) |

Where the effort went:

- **Calls:** 632 in total; **410 of them (65%) were spent on the 23 failed tasks**.
- **Solved tasks:** a solved task took 1.63 calls on average (median 1). 94 of the 136 were solved with a single call.
- **Step outcomes over all 632 calls:**

| Outcome | Calls |
|---|---|
| applied | 355 |
| unproved | 176 |
| unreadable | 55 |
| false (the prover found a counter-example) | 34 |
| refused (the `bind` depth rule) | 8 |
| network | 4 |

- **The 55 unreadable replies:** 21 failed the L_spec parser; 34 parsed but did not type-check in Lean.
- **Retractions:** 33 in total.

## 3. Why the 23 tasks failed

Each failure is assigned to one cause. The cause is read from the per-step feedback in the results file and from a
comparison with the hand-written (gold) derivation in `exports/all_derivations.json`.

| Cause | n | Tasks |
|---|---|---|
| A. Beyond the prover: the gold derivation fails too | 9 | he_001, 025, 059, 071, 087, 099, 111, 114, 129 |
| B. `digits` was misunderstood: its result type is missing from the cheatsheet | 4 | he_044, 079, 084, 103 |
| C. No computable way to pick a witness | 3 | he_069, 090, 094 |
| D1. Sort comparator in a form the prover's lemma does not match | 2 | he_116, 149 |
| D2. A design the prover cannot close, where gold uses a different one | 5 | he_009, 020, 037, 118, 136 |

**Gold-reachable failures:** excluding A leaves 14 tasks that the gold derivations show are reachable under the same
prover. 136 + 14 = 150, which is the strict ceiling.

### A. Beyond the prover (9)

Strict gold fails exactly these 9 tasks (paren groups, prime factors, rounding a square root or a decimal, a nested
flatMap, `foldl` min/max over a computed list). Under the strict protocol the model cannot get past what the prover can
prove, so these 9 tasks are outside its reach until the prover improves.

### B. `digits` was misunderstood (4)

- **What the translator does:** L_spec `digits(b, n)` translates to Lean `Nat.toDigits b n`. That returns the digit
  **characters**, most significant first: `digits(2, 5) = ['1','0','1']`.
- **What the cheatsheet says:** only the row `` `digits` | `Nat.toDigits` ``. It does not say what the result is.
- **What the model assumed:** that the result was a list of numbers.

How this played out in each task:

- **he_079, he_084, he_103:** the model wrote `string(digits(2, n).map(lambda d: '0' if d == 0 else '1'))`.
  - Lean rejects this with `failed to synthesize OfNat char 0`: `d` is a character and is compared with `0`.
  - The correct answer was simply `string(digits(2, n))`, which is the gold derivation for he_079 and he_084.
- **he_044:** the gold derivation is one term, `String.mk (Nat.toDigits base x)`. Not knowing that `digits` already
  gives the string's characters, the model built a base-conversion loop instead. The prover could not close its exit
  condition, and the task ran out after 4 attempts.

### C. No computable way to pick a witness (3)

Each of these tasks needs "the element of the list with property P".

- **What the model did:** it first split on `exists x in lst: P(x)`, then named the witness with nested `bind` steps.
  Once those reached the depth limit of 3, the 4th `bind` was refused (8 refusals across the three tasks).
- **Its next attempts:** after the refusals, the model wrote Lean syntax inside L_spec:
  - `Classical.choose h1`, rejected by the parser with `trailing 'h1'`;
  - `Classical.choose (not_forall.mp h19)`, rejected with `trailing '('`;
  - `lst.find(...)`, which translates to `List.find`. Lean has only `List.find?`, so this failed with
    `Invalid field 'find'`.
- **he_069:** the session accepted a derivation that used `Classical.choose`, and the task was CERTIFIED. The
  fresh-process compile then rejected it: `failed to compile definition, consider marking it as 'noncomputable'`.
  Noncomputability is only detected when the final certificate is compiled, not when the step is applied.
- **What the gold derivations do:** they avoid witnesses altogether, using a single scan loop for he_069 and he_094,
  and cases + bind + loop for he_090.

### D1. Sort comparator form (2)

For he_116 and he_149, the model's program is the gold program, but its comparator is written in a different form:

| | Comparator in Lean |
|---|---|
| Model (after translation) | `decide ((ones a < ones b) ∨ ((ones a = ones b) ∧ (a ≤ b)))` (one `decide` of a proposition) |
| Gold | `decide (ones a < ones b) \|\| (ones a == ones b && decide (a ≤ b))` (Boolean connectives) |

The prover library's lemma for "sort by a key, then by the order" (`Refine.mergeSort_key_then_le`, `lemmas.py`) is
stated for the Boolean form, so it does not fire on the model's form. Strict gold solves both tasks. The model gave the
same answer 4 times and ran out.

(he_149 has a second difference: the model wrote `a <= b` on strings, where gold wrote `!decide (b < a)`.)

### D2. A design the prover cannot close (5)

The model chose a single loop (or one large term) whose invariant speaks about list prefixes and appends. The prover
could not prove that the loop update keeps such an invariant, even when the update was correct. For example, in he_009
the update `(i + 1, acc ++ [numbers[i]])` under `acc[i-1] <= numbers[i]` was refused 4 times.

| Task | Gold derivation | Model's derivation |
|---|---|---|
| he_009 | one closed-form term: a map over `range` of `foldl max` on prefixes | a loop |
| he_037 | one closed-form term | a closed form first (unproved), then a loop |
| he_020 | loop → bind → loop → cases | one large term, then a loop |
| he_118 | bind → loop, then cases | one loop |
| he_136 | bind → loop, twice | one loop over three state variables |

In he_118, 3 calls were also lost to OpenAI network errors.

### Wasted calls across causes

Of the unreadable replies, 21 failed the parser. In most of them the model wrote Lean syntax inside L_spec:

- type ascriptions: `(-1 : rat)`, `('0' : char)`;
- application by juxtaposition: `Nat.toDigits 2 x`, `a.getD 0`, `List.cons a b`, `indexOf 1`, `Classical.choose h`.

The parser's messages (`Unsupported: trailing 'h1'`, `expected ')', found ':'`) do not say what to write instead, so
the model often repeated the same mistake. These replies occur in he_069, 071, 090, 094, 099, 103, 111, 129 and 136.

## 4. Fixes, and which approach each one reaches

We compare three approaches:

- **L_spec joint:** one call per step.
- **L_spec split:** a selector call picks the law and a plan, then an applier call writes the step.
- **Direct Lean:** `LeanAgent`; the model writes Lean directly.

All three share the engine (`engine.py`), the prover (tactics + `lemmas.py`) and the fresh-process check. Only the two
L_spec approaches use the translator, the cheatsheet, the parser and the `bind`-depth rule.

| Fix | Cause | Layer | L_spec joint | L_spec split | Direct Lean |
|---|---|---|---|---|---|
| Say in the cheatsheet that `digits(b, n)` is the list of digit characters; give `string(digits(2, n))` as the binary string | B | cheatsheet | yes | yes, but the **selector prompt has no cheatsheet**, and the selector is the one that picks loop vs term (he_044). It needs this line too. | not needed: the model sees `Nat.toDigits` directly. An optional line in `LEAN_RULES`. |
| Parser messages that name the fix ("write `f(x, y)`, not `f x y`"; "no `(x : T)`"), or accept `(e : T)` | wasted calls | parser | yes | yes | n/a (Lean's own errors) |
| Translate `find` to `find?` (or give `first(lst, p)` returning an option) | C | translator | yes | yes | n/a |
| Refuse a step whose term is not computable (e.g. `Classical.choose`) when it is applied, not at the final compile | C | engine | yes | yes | yes: the same certificate path, and the Lean agent forbids `Classical` only in its prompt |
| In `split`, send a `bind`-depth refusal to the selector at once. The applier is locked to the law "bind", so it can only repeat the refused law until the goal fails twice. | C | split routing | n/a | yes | n/a |
| Normalise `decide (p ∨ q)` / `decide (p ∧ q)` to `decide p \|\| decide q` / `&&` before the sort lemmas, or state the lemmas for both forms | D1 | prover | yes | yes | yes: a model writing Lean can produce either form |
| More prefix/append lemmas for loop invariants | D2, part of A | prover | yes | yes | yes |

**Rule for the comparison:** wherever possible, a fix goes in the shared layer (engine or prover), so that all three
approaches gain from it equally. Fixes in the translator, cheatsheet or parser are part of the L_spec contribution and
should be reported as such.

## 5. Notes for the paper

- **The fixes were tuned on the test set.** The fixes in §4 come from HumanEval failures. Report them as such, and
  confirm them on a benchmark not used to find them (Verina or the classic set) before claiming a general gain.
- **Re-check gold after every prover change.** After any change to the prover, re-run strict gold on all 159 tasks
  and report the ceiling again (it is 150 now). A normalisation rule must not lose a gold task.
- **This is a single trial.** There is one trial per task at temperature 0.2. Variance across trials is not measured.
- **Reachable tasks.** Excluding the 9 tasks gold cannot do (A), the model solved 136 of the 150 gold-reachable tasks
  (90.7%).
- **he_069 counts as a failure.** Count it as failed in the main table, but state why: it is the only case where the
  session accepted a derivation the fresh compile rejected.
- **The joint run's certificate files are gone.** That run wrote its certificates over the committed gold files in
  `verified/`. While separating them on 2026-11-10, the model's 137 files were lost, and gold was restored from git.
  The verdicts (each one a fresh-process compile) and every derivation tree are kept in the results file.
  `lspec_run.py --model gold --trees <results file> --tag <name>` rebuilds the files with no model calls. Since commit
  2df2fad, every run writes its certificates to `verified/<dataset>_<tag>_<workflow>/` and records the path in each row.

## 6. Fixes applied, and the re-run of the failures (2026-11-10/11)

### Fixes (commit 2df2fad, plus `append_mk_eq`)

| Fix | Cause | Layer | Reaches |
|---|---|---|---|
| Five `MEANING` lines in the cheatsheet: `digits` (characters, most significant first; `Nat.digits` for values), `find?`, `index`, `split` keeps empties, call syntax. Each claim was checked in Lean. | B, C, wasted calls | cheatsheet | L_spec joint and split. The library lines (`LIBRARY_FACTS`) are also in the split **selector** prompt. |
| `(e : T)` is read as `(e as T)`; `find` is read as `find?`; a parser error caused by Lean-style application or by `Classical` gets a hint saying what to write | C, wasted calls | parser | L_spec |
| `Classical.` in a field that must run (term, condition, initial value, guard, result) is refused when the step is applied (`laws.py`) | C | engine | all three approaches |
| In `split`, a refusal of a bind past the depth limit goes to the selector, and a selector that picks `bind` at the limit is refused before any applier call | C | split routing | split |
| `mergeSort_key_then_le_prop`, `mergeSort_key_then_not_lt_prop`: the two sort lemmas restated for the comparator written as one `decide` of a proposition | D1 | prover | all three |
| `append_mk_eq`: `s ++ String.mk l = String.mk (s.toList ++ l)`, in both rewrite sets | he_103 (below) | prover | all three |

### Checks made without the model

- **Round trip:** every expression of the corpus still goes Lean → L_spec → Lean unchanged: HumanEval 1238/1238,
  classic 42/42, Verina 1033/1033, both before and after the parser change.
- **Gold steps vs. the `Classical` rule:** no step of any gold derivation (HumanEval, classic, Verina) is refused by it.
- **Gold re-run on the 14 gold-reachable failures** after the prover changes: 14/14 verified in a fresh process
  (`run_humaneval_gold_recheck1110_joint.jsonl`).
- **The model's own he_116 and he_149 terms**, replayed with no model calls: 2/2 verified
  (`run_humaneval_gold_modelterms1110_joint.jsonl`). The prover had refused both 4 times in the joint run.

### Model re-run on the 14 gold-reachable failures

Results files: `run_humaneval_openai-gpt-5.4-mini_ex2cross_fix1110_joint.jsonl` (14 tasks), and
`..._fix1111_joint.jsonl` (he_103 again, after `append_mk_eq`). Same settings as §1. Cost: $1.40 + $0.01.

**11/14 solved and verified in a fresh process** (10 in the first re-run, then he_103 after `append_mk_eq`). 10 of
the 11 took at most 9 calls (he_069 took 16). In the joint run, these 14 tasks had used 261 calls with no success.

| Task | Joint run | Re-run | Fix that applies |
|---|---|---|---|
| he_037 | exhausted, 28 calls | **solved, 1 call** | cheatsheet (the closed form now proves) |
| he_044 | exhausted, 4 | **solved, 1** | `digits` line: `string(digits(base, x))` instead of a loop |
| he_069 | failed the fresh compile (`Classical.choose`) | **solved, 16** | `Classical` refused at the step |
| he_079 | exhausted, 4 | **solved, 1** | `digits` line |
| he_084 | exhausted, 4 | **solved, 1** | `digits` line |
| he_094 | exhausted, 30 | **solved, 9** | `find?`; `Classical` refused |
| he_116 | exhausted, 8 | **solved, 3** | sort lemma, Prop-form comparator |
| he_118 | exhausted, 30 | **solved, 9** | (no targeted fix; 3 calls were lost to the network in the joint run) |
| he_136 | exhausted, 25 | **solved, 2** | (no targeted fix: the model chose a different loop) |
| he_149 | exhausted, 4 | **solved, 1** | sort lemma, Prop-form comparator |
| he_009 | exhausted, 27 | exhausted, 23 | — (D2: a loop the prover cannot close) |
| he_020 | exhausted, 16 | exhausted, 30 | — (D2) |
| he_090 | exhausted, 30 | exhausted, 30 | — (the 2-element case: `some(max)` is unproved against the specification's form) |
| he_103 | exhausted, 24 | exhausted, 30; then **solved, 3** (fix1111) | `digits` line, then `append_mk_eq`. In the first re-run the model wrote `some("0b" ++ string(digits(2, …)))` at once, but the prover could not close the string append (gold builds the list inside `String.mk`). With `append_mk_eq`: the replayed model term verified, gold he_079/084/103 still verified (3/3), and the model solved it in 3 calls. |

Two of the 10 (he_118, he_136) have no targeted fix. This is single-trial variance as much as the fixes, and should
be reported as such.

**Final count:** joint (136) + re-runs (11) = **147/159**. Policy: a task that is solved stays marked as a success for
its configuration and is never re-run. Only failures are re-run. The 136 were solved before the fixes and the 11
after. The fixes only add facts and rewrites, and refuse steps that cannot run, so they don't take away anything an
earlier solution used.
