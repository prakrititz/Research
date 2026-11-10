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
- **Certificates are overwritten.** Every `lspec_run.py` run writes its certificates to `verified/<task>.lean` in this
  folder, replacing whatever is there, including the committed gold files. After this run, those files hold the model's
  certificates, and he_000/he_001 hold the split run's. Gold can be restored from git. The folder should be named per
  run before the next run.
