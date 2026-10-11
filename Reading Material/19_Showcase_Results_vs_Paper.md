# 19 — Showcase: our results next to the paper's (2026-10-05, final)

> **Read this first if you have ten minutes before meeting Dr. Hou.** What the paper reports, what we measured, and how sure we are. Every number is `[ran]` (measured on your laptop with the hosted `gpt-oss:120b`, low reasoning effort, unless a row says otherwise) and comes from a file in `benchmarks/results/`. The paper-style version is `20_Paper_Draft.md` (LaTeX: `paper/main.tex`, figures `paper/fig_*.png`); the talk is `21`. An independent review session re-checked these numbers from the raw rows (`10`, its entry of 2026-10-05).
>
> **The model server is down until its tunnel's bandwidth limit resets** (from about 09:10 on 2026-10-05 every call returned `HTTP 403: This ngrok account has reached its network bandwidth limit for the month`). Use the offline demo in §8.

---

## 1. The story in one paragraph

The paper (Refine4LLM) lets an LLM choose refinement laws while a prover checks every step, and reports **150 / 164** HumanEval problems verified and passing all tests. We rebuilt it with an open model, Z3 for the search and **Coq and Lean** as independent checkers, and asked what the paper does not report: *how often does it work if you run it again?* At first: **7 times in 10** on the paper's own square-root example. Every failure we read was caused by **what the system told the model after a failed step**, not by the prompt. With general fixes (nothing square-root specific) the final code (v8) succeeded **100 times in 100**, two model calls in the median run, every derivation re-checked by Coq; it solves all 11 other benchmark problems **20 times out of 20** (220 / 220, and again 220 / 220 in a second run) and never "proves" an impossible specification. On HumanEval, two 2025 open models *alone* already pass more tests than the paper's GPT-4 did; refinement with our untuned model derives **verified programs for the simple problems every time** and rarely for loops and searches. Executing every derived program exposed ways a valid proof can still give an unrunnable program, **one wrong step that the search prover accepted — which Coq refused to certify and the tests caught** (§6), and **a gap in the paper-style termination rule** that let a never-ending loop through (§7) — fixed in v9.

## 2. Same type of results as the paper

| The paper reports | What we measured | Same direction? |
|---|---|---|
| **Table 6:** GPT-4 alone 145 / 128 (HumanEval / EvalPlus); Refine4LLM **150 / 150** | Models alone, all 164: `gpt-oss:120b` **156 / 147**, `qwen3-coder-next` **154 / 147**. Refinement on the 20 problems our language can state, with *checked* specifications: a verified program that passes every test in **41 of 121 runs**, for 7 of 20 problems (§5) | Baselines: ours are stronger than GPT-4. Refinement: every derived program that runs correctly on the original tests also passes EvalPlus, except one that is too slow (no EvalPlus drop — the paper's key qualitative claim); coverage is far below 150 |
| **Table 7:** classic programs, extended laws need fewer steps than core laws | Factorial, Exponentiation, Linear Search, Max Element: **one step fewer** with the extended law in every case; all obligations certified by **Lean (21 / 21)**, Coq 9 / 21 (`16`, §6) | Yes (smaller effect; the paper also uses learned laws) |
| **Table 9:** ablation | Ablations of *our* components: leaf assist on/off, strict vs relaxed termination, reasoning effort, old vs fixed code (§3, §5) | Same kind of table, different components |
| Fig. 2: square root derived by refinement | Derived **100 / 100** times with v8 (95 % CI 96–100 %); the paper's exact Fig. 2 invariant is rejected by our prover because it lacks `x ≥ 0` — question Q1 for Dr. Hou | Yes, with a finding to discuss |
| Table 8: law library | not reproduced (no learned library) | — |

## 3. Reliability on the paper's example (the result the paper does not have)

| Code | What changed | Square root, successes | 95 % interval |
|---|---|---|---|
| v3 | general prompt + first engine fixes | 7 / 10 | 40–89 % |
| v4 | the parent is told *which fact* is missing (`x ≥ 0`) | 29 / 30 | 83–99 % |
| v5 | sub-problems must be solvable; invented names refused | 99 / 100 | 95–100 % |
| v6 | splits on meaningless tests refused | 99 / 99 (+1 trial lost to the network) | 96–100 % |
| **v8** | faithful formula display, typed and executable steps, provers aligned | **100 / 100** (two independent sets of 50; median 2 calls, max 4; all Coq-certified; both distinct programs pass 212 concrete inputs) | **96–100 %** |

Figure: `paper/fig_reliability.png`. From 7/10 to 99/99 is far beyond noise (Fisher exact test p = 0.0006).

| Arm (square root) | Successes | 95 % interval | Note |
|---|---|---|---|
| v8, `reasoning_effort = medium` | **20 / 20** | 84–100 % | median 2 calls; slower calls (32 s per trial) |
| v6, strict termination rule (`0 ≤ V < V0`) | 46 / 48 | 86–99 % | median 3 calls; not significantly lower than relaxed (p = 0.11), just slower |
| v6, **assist off** | **8 / 30** | 14–44 % | the model picks the right loop, then answers the trivial `x := 0` / `x := x + e` with more loops (p ≈ 2 × 10⁻¹⁸ vs on) |
| v8, assist off; second model (`qwen3-coder-next`) | not measured | — | the model server was cut off (bandwidth limit) before they ran |

The leaf assist is the largest single factor. It is not in the paper; it plays the role the paper's instruction-tuned GPT-4 played for the boring steps, and it only *proposes*: every step it takes is proved like the model's.

## 4. Generality: the other benchmark problems (v8)

All 11 other solvable problems, 20 trials each: **220 / 220** (each 95 % interval 84–100 %), median 2 calls, every derivation Coq-certified — and **220 / 220 again** in a second complete run (there Coq certified 218: in two division derivations its tactics could not close one step; nothing was refuted). Integer division, which failed 19 of 20 times before the two-assignment search existed, is now **20 / 20, twice**. The impossible specification (negative control): **0 / 5, twice**. Running the derived programs: all correct except one division derivation whose program reads a variable before assigning it (legal in the calculus, where every variable always has *some* value; a crash in Python) — fixed in v9 by giving such variables a start value.

## 5. HumanEval: 20 checked specifications

Our specifications are **checked by machine, not by eye**: for every HumanEval and EvalPlus input the reference answer must satisfy the specification (83 to 1011 inputs per problem; inputs whose quantifier ranges are too large to enumerate are reported as unchecked — e.g. 581 of `gcd`'s), and every deliberately wrong answer must be rejected (590 / 590). For 17 of the 20 a hand derivation is accepted by the engine, so a failure there is the search's, not the engine's.

**v8, 121 runs** (each problem 4 to 8 times; 5 further runs cut off by the server outage are not counted; figure `paper/fig_pilot.png`; per-problem table `python benchmarks/pilot_compare.py`):

| Tier (what the program needs) | Runs that derived a program | Problems with a verified program that passes every test |
|---|---|---|
| A — one assignment or a case split (6) | **35 / 42** | 6 of 6: `car_race_collision` 6/6, `triangle_area` 8/8, `add` 8/8, `is_equal_to_sum_even` 6/6, `right_angle_triangle` 6/6 (every run, 2 calls); **`multiply` 1/8** |
| B — a loop or a chain of cases (5) | 7 / 29 | 1 of 5: `sum_to_n` 6/6 |
| C — searches with nested quantifiers (9) | 11 / 50 | 0 of 9 (see below) |

* **41 of the 53 derived programs pass every original and EvalPlus test, and all 41 are fully certified by Coq.** (Coq fully certifies 45 of the 53: those 41 plus 4 valid but unrunnable ones.)
* **A real win over the model alone:** `multiply` — the direct model fails EvalPlus; one refinement run derived a verified program (25 calls) that passes every original and EvalPlus test.
* **The 12 derived programs that fail a test are all understood:** 8 assign a quantified formula (`t := exists k. k*k*k = a`), which no program can run; 1 tests the proof-only name `V0`; 1 (`gcd`) is correct but too slow for EvalPlus's 13-digit inputs; 1 is the wrong step of §6; 1 is the never-ending loop of §7. Executing the programs found every one; v9 refuses all of these kinds (`20`, §7.5).
* **Held-out problems** (the 8 specified after the v8 fixes): `add` and `triangle_area` every time, `multiply` once; of the other five, two (`monotonic`, `triples_sum_to_zero`) were derived once each but only as unrunnable quantified assignments, three never.
* **Compared with the old code** on the original 12 (29 runs): 13 derived then, all passing; v8 lifts `is_equal_to_sum_even` from 1/3 to 6/6 (the display fix) and still fails the array loops.

**Reading it:** with this untuned open model, refinement is reliable for simple problems and rarely finds loops over arrays or nested-quantifier searches, although hand derivations exist. The failures are explained one by one in `20`, §7.5.

## 6. One wrong step got through — and was caught

In one of the HumanEval runs (`gcd`, file `he_refine_v7.jsonl`, row 21), the leaf assist closed a sub-problem with `x := g * k` whose proof obligation is **false** (for a = b = 4 the middle assertion allows g = 1, which is not the greatest common divisor). Z3 must have answered "proved" in that run, although offline the same obligation is answered "counterexample" or "unknown" every time we ask (41 seeds and 1,698 repeats with random time limits on this laptop; four complete re-runs of the assist's search, about 3,700 Z3 queries; more than 1,500 runs in the review session's Linux build), and replaying the stored run does not accept it — not even when the 21 runs before it are replayed first in the same process, which reproduces those 21 exactly. Two independent safeguards caught it: **Coq refused to certify the derivation** (0 of 2 obligations) and **the program failed the tests**. It is the only such case found among the night's derivations; every derivation counted as a success above is Coq-certified. The cause is under investigation (`benchmarks/probe_wrong_step.py`); until it is known, a derivation counts as verified only when an independent kernel (Coq or Lean) has certified it — which is how §2–§5 count.

## 7. A gap in the paper-style termination rule (found by running the programs)

The runs used the *relaxed* termination rule (the loop measure only has to decrease, `V < V0`, as the paper's Lemma 6.7 reads; our default is the stricter `0 ≤ V < V0`). In one `gcd` run the model's loop `while g is not a common divisor: g := g + 1` with measure `a − g` was accepted — the measure does decrease every time — but **the program never stops** when `a` does not divide `b`: `g` grows past `a` and the measure goes negative for ever. Over the natural numbers (Coq's `nat`) `V < V0` is enough; over the integers it is not.

* **Every success counted above is safe:** for all 265 loops the model proposed in successful runs whose measure could be checked, the invariant and the loop test imply the measure is ≥ 0 (checked with Z3), so for them relaxed and strict coincide; the only unbounded measure in a counted success belongs to a proposal that was refused.
* **The fix, and a resolution of decision D1:** v9 keeps the paper's `V < V0` and adds the obligation *"while the loop runs, the measure is never negative"* (`I ∧ G ⇒ 0 ≤ V`). This is sound for integers and still accepts the paper's own measure `N − (x+e)²`, which is only negative after the last iteration. It refuses the `gcd` loop; 90 of 90 stored square-root and loop derivations replay identically under it (tests: `tests/test_v9_termination.py` in the v9 copy). Question for Dr. Hou: are the paper's measures naturals?

## 8. Demo (5 minutes)

**Offline (works now, with the model server down):**

```bash
python benchmarks/replay.py "benchmarks/results/reliability/v6_relaxed_assist_*.jsonl" --rows 0 1 --assist --strict 0 --certify coq
```

It feeds two stored trials' model replies back through the engine and prints, for each, `recorded SUCCESS/… calls, replayed SUCCESS/… calls -> same | coq: 3/3`. The stored replies of the second trial are just two short JSON answers — the law (`initialised_iteration`) and the loop (`invariant: x * x <= N && x >= 0`, `guard: N >= (x + e) * (x + e)`, `variant: N - x * x`); the set-up `x := 0` and the body `x := x + e` are closed by the assist with no model call, and the program is `x = 0; while N >= (x+e)*(x+e): x = x + e`.

**Live (once the tunnel's bandwidth limit has reset or been raised):**

```bash
export FORMALLLM_REMOTE_AUTH="$(cat "$HOME/.formalllm/remote_auth")"
export PATH="$HOME/.formalllm/rocq/bin:$PATH"
python main.py --case C5-sqrt-paper --config gpt-oss-120b-low --assist --certify coq lean
```

## 9. What is new (things to claim, with evidence)

1. **A reliability protocol** for LLM-guided refinement: many trials, confidence intervals, every model reply stored and **replayable offline** (`replay.py`).
2. **Failure classes, each fixed by a general engine rule** — ten found before and during the night (`20`, Table 1), six more found by executing the HumanEval programs and fixed in v9.
3. **The provers did not agree on what a formula means** — integer division by negative numbers, arrays of floats, Booleans. All aligned and pinned by tests.
4. **Defence in depth works:** a step the search prover accepted wrongly was refused by Coq and caught by the tests (§6); a never-ending loop accepted by the relaxed termination rule was caught by the tests (§7).
5. **A termination rule that is sound for integers and accepts the paper's measure** (§7, v9).
6. **Checked specifications** (reference outputs on every enumerable test input + mutation testing) — a way to trust hand-written specifications that the paper describes only as "manually checked".
7. **An updated baseline:** two open models alone pass 156 / 147 and 154 / 147 — the paper's improvement over GPT-4 is absorbed by the models; refinement's value is the guarantee.

## 10. What not to claim

* Not "we reproduced 150 / 164": we cover 20 problems that our language can state, and refinement solves 7 of them.
* Not "refinement beats the model on tests": the models alone are already very strong (gpt-oss fails 2 of these 20; refinement fixed one of them, `multiply`, once in 8 runs).
* Not "Z3 alone is enough" (§6), and not "relaxed-rule derivations always terminate" (§7): certification by Coq or Lean, bounded measures and executing the programs are what make the counted successes trustworthy.
* Not "fast": some derived programs are proved correct but too slow for EvalPlus's largest inputs.
* One model family for refinement, mostly low reasoning effort.

## 11. A note on the result files of 2026-10-05

* **Two launchers ran the same v8 code side by side** during the night (an earlier launcher I believed stopped kept running). Its files are labelled `v7_sqrt_assist_*`, `v7cases_*` and `he_refine_v7.jsonl`; they are **v8-code runs** (the code did not change after 23:08, source fingerprint `8ae219421b4fd444`) and are counted above as additional samples. They are unrelated to the "v7" of the evening of 10-04.
* **From about 09:10 the model server's tunnel refused every call** (monthly bandwidth limit). Runs after that — the second model's square-root arm, v8 without the assist, a no-assist repeat and the last 5 pilot runs — never reached a model and are **not counted** (`FormalLLM/llm/transport.py` now recognises this cut-off, so summaries leave them out automatically).
