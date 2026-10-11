# 12 — The Paper vs. Our Implementation (gap analysis)

> **Read `11_The_Paper_Explained.md` first.** This file compares what the paper *says* with what our code *does*, and lists the decisions I need from you **before I change any prompt or law**. Nothing below has been changed yet (apart from the small Z3 robustness fixes recorded in `10_Progress_Log.md`).
>
> **Evidence tags:** `[paper]` quoted from the PDF · `[code]` read from the repo (file:line) · `[offline]` I ran it on this machine with no LLM · `[log]` taken from the committed run logs · `[live]` from the run I started today (see §6).
> **Honesty rule:** a `[hypothesis]` tag means "plausible, not yet proven".

---

## 1. Bottom line

1. **The laws we implemented match the paper's.** Skip, assignment, sequential, alternation, strengthen/weaken, initialised skip, flexible sequential, iteration, initialised iteration — each corresponds to a numbered lemma. One is deliberately corrected (flexible sequential: the paper's statement has `Q ⇒ D`, its own proof needs `D ⇒ Q`, we use `D ⇒ Q`). `[code][paper]`
2. **The prover is *not* why sqrt fails.** Z3 checks the entire three-step sqrt derivation in **0.018 s** `[offline]`. The paper used Coq + CoqHammer; switching to Coq/Lean would not change the sqrt outcome. It matters for *trust* and for harder obligations (quantifiers, arrays), not for this example.
3. **The cost is the LLM, not the logic.** In the committed `gpt-oss-120b` run, plain code generation took 193 s for one call; refinement took 675 s for **10** calls (≈ 67 s per call). `[log]`
4. **Where we plausibly diverge from the paper in a way that hurts sqrt** (details in §2–§5):
   * we ask the LLM for **more** than the paper does (a *variant* on top of invariant and guard);
   * we **reject more** than the paper does (strict `0 ≤ V` termination rule by default) — this makes runs *costlier* (4 vs 9 calls in the one successful run) but, in the existing ablation, did not change *how many* runs succeed (§4.1);
   * our **prompts are thin** (one-line law blurbs, no instantiated proof condition, no syntax rules in the law-choice turn, a `sqrt` hint baked in) — which is exactly your professor's complaint;
   * our **failure feedback is thinner** than the paper's (law choice sees only a blacklist; a failed child gives the parent no spec and no counterexample);
   * our **retry policy is harsher** (2 tries then the *law* is blacklisted; paper: more than 5 failures before falling back);
   * the paper used **GPT-4 + instruction tuning on Morgan's examples**; we run open models zero-shot.
5. **The paper reports no sqrt success rate**, so "follow the paper's result" can only mean (a) reproduce its *mechanism* on sqrt (propose → verify → counterexample → retry → backtrack, as in Figs. 2/3/9) and (b) approximate its *tables* (6–9). I need you to confirm which (§7, decision D0).
6. **The paper's own Fig. 2, replayed exactly, does not pass our engine in either termination mode** (counterexample `x = −3, e = 1, N = 10`); it passes only if the loop body must merely preserve the invariant, i.e. *partial* correctness (§4.0). That is a concrete question for Dr. Hou (Q1 in §7) and it sets what "reproducing the paper" can honestly mean.
7. **A live `gpt-oss-120b` run (1 trial, §6)** found the paper's Fig. 2 decomposition by itself, then lost 27 of its 40 calls in a loop-body subtree that could never succeed (credit assignment), and at the very end discarded its own *correct* answer because it used the keys `I/G/V` (G17). The budget stop was also mislabelled `EXHAUSTED` (G16). Result: no program, 1,668 s.

---

## 2. Side-by-side

Legend: ✅ same · ⚠️ different · ❌ absent in ours.

| # | Topic | The paper | Our code | Verdict |
|---|---|---|---|---|
| G1 | **What the LLM supplies for a loop** | Table 5 (p.16): invariant **I** and guard **G** only. Variant "can be extracted from the specification" (§10.1 p.22) `[paper]` | `initialised_iteration` needs invariant + guard + **variant** (`laws/initialised_iteration.py` PARAMS; `llm/prompts.py:60`); `iteration` needs guard + **variant** `[code]` | ⚠️ |
| G2 | **Termination rule** | Core Lemma 2.7: `0 ≤ V < V₀`, integer. Extended Lemmas 6.6/6.7: no integer/lower-bound requirement, runtime `assert V ≠ V₀`; §11.3: otherwise "partially correct" `[paper]` | Default **strict** `0 ≤ V ∧ V < V₀` (`initialised_iteration.py:55`, `iteration.py:89`; env `FORMALLLM_STRICT_VARIANT`). The prompt text hard-codes "bounded below by 0" (`prompts.py:237,243`) even when the toggle is off `[code]` | ⚠️ |
| G3 | **The "condition" the LLM sees** (Alg. 1 line 7→8) | System derives the proof condition from (spec, law) and gives it to the LLM `[paper]` | Static blurbs; spec-instantiated obligations only for `iteration` / `initialised_iteration` (`prompts.py:230-244`) and they print the parameter header inside the formula (`Q = (N:float)(e:float) := …`) `[offline]` | ⚠️ |
| G4 | **Rules "included in the context"** (§8.2) | All rule details in every prompt `[paper]` | Law-choice turn has the law blurbs but **no expression syntax** (`generate_law_selection_prompt` omits `SYNTAX_HELP`). Models then propose `sqrt(...)` assignments (committed `gpt-oss-120b` log) `[code][log]` | ⚠️ |
| G5 | **Feedback to law selection** | On fall-back the LLM gets "detailed feedback about the failures and the counterexamples, along with the last valid specification" (§7.2 p.16) `[paper]` | Law-choice turn gets only a list of blacklisted law names (`prompts.py:201-202`); history appears only in the parameter turn and in single-turn mode `[code]` | ⚠️ |
| G6 | **Feedback from a failed sub-spec** | Modular verification: the LLM gets "feedback specific to that module, including failure reasons and counterexamples" (§7.2) `[paper]` | Parent records only `"Child node 'N2' exhausted all options. Blacklisted: [...]"` (`agent/refiner.py:~196-199`) — no child spec, no counterexample `[code]` | ⚠️ |
| G7 | **Retry / fall-back** | `FailCount > 5` → `FallBack` (Alg. 1 lines 14-17) `[paper]` | Multi-turn: **2** parameter tries (`max_param_attempts=2`, `refiner.py:39`), then the *law* is blacklisted for that node (`:205-206`, `:229`); node gets `max_retries` attempts (4 in the harness) `[code]` | ⚠️ |
| G8 | **LLM calls per step** | Two: `law ← LLM(spec)`, `code ← LLM(spec, law, condition)` `[paper]` | Benchmark harness: two (`harness.py:121 use_multi_turn=True`) ✅. Interactive `main.py`: single call ⚠️ `[code]` | ✅/⚠️ |
| G9 | **Law set** | Core: strengthen, weaken, skip, seq, assign, alternation (multi-guard), iteration, expand, assertion, procedures. Extended: 6.1-6.8 `[paper]` | 10 laws. Missing: initialised assignment (6.3), following assignment (6.4), **assertion iteration (6.7)**, traverse (6.8), multi-guard alternation (2.6), expand (2.8), assertion (2.9), procedures (2.11/2.12). L_pl has no `assert` or `def` (`lpl/ast.py`) `[code]` | ❌ |
| G10 | **Library of refined specs; law learning** | RQ2/RQ3, Algorithms 2-3, Table 8 (fall-back 26.87 % → 9.45 %, pass 52 % → 82 %) `[paper]` | None. GitHub issue #3 / "M6" is the placeholder `[code]` | ❌ |
| G11 | **Prover** | Coq + CoqHammer (cvc4, Vampire, E, Z3) `[paper]` | Z3 only `[code]` | ⚠️ |
| G12 | **The LLM** | GPT-4, instruction-tuned on Morgan's examples and the extended laws; refinement calculus given as retrieved background `[paper]` | llama3.1, qwen3.5, ornith (local, 8-10B); gpt-oss-120b, qwen3-coder-next (hosted); zero-shot `[code]` | ⚠️ |
| G13 | **Benchmarks** | 164 HumanEval/EvalPlus problems with hand-checked formal specs + CorC classic examples `[paper]` | 13 hand-written cases (A:4, B:3, C:5, D:1); only 2 have runnable test cases `[code]` | ❌ |
| G14 | **Metrics** | pass count, #steps, proof time, refinement time, fall-back rate, program size `[paper]` | outcome, LLM calls, wall time, tokens, attempt statuses (`harness.py:163-182`) — partly overlapping | ⚠️ |
| G15 | **Measurement validity** | 164 problems, one run each, GPT-4 `[paper]` | cells of n = 1-2; transport/credential errors recorded as model failures (§4.3) `[log]` | ⚠️ |
| G16 | **Budget stop is swallowed** | n/a | `refine_node`'s blanket `except Exception` (`agent/refiner.py:231`) catches the harness's `BudgetExhausted` (defined in `benchmarks/harness.py:17`, outside the package), logs it as a failed *attempt*, and keeps looping; the run is reported `EXHAUSTED`, not `BUDGET`. In the live run 23 of 34 recorded errors were this message `[code][live]` | ⚠️ |
| G17 | **Reply-format brittleness** | code in a fixed template `[paper]` | the schema example shows placeholders (`"invariant": "I"`); the model replied with keys `I/G/V` and a *correct* loop was discarded; the parser takes exact key names only (`llm/parser.py:242`) `[code][live]` | ⚠️ |

### 2.1 Where each gap stands now (2026-10-03, end of day) and four new ones

| # | Status | What changed |
|---|---|---|
| G3, G4 | **closed** | every prompt now shows the proof condition instantiated for the current specification, and the expression-language rules are in both turns (`13`) |
| G5, G6 | **closed** | the law-choice turn gets the history of what failed; a parent gets the failed child's specification, the failed proof, its counterexample and — when the system can tell — which of its own parameters to change (`13`, §5.1) |
| G7 | closed | three parameter tries per law before it is set aside (the paper falls back after more than five failures per specification) |
| G8 | **closed** | `main.py` is now a real two-turn command line |
| G11 | **partly closed** | Z3 searches; Coq and Lean 4 re-check finished derivations; `z3+lean` lets Lean prove what Z3 leaves undecided. Still no CoqHammer with external provers (`15`) |
| G13 | **partly closed** | a 12-problem HumanEval pilot with checked specifications; the paper's own specifications are still missing (`16`, `18`) |
| G16, G17 | **closed** | with tests |
| G1, G2, G9, G10, G12, G14, G15 | open | unchanged. G15 improved: studies now report counts with 95 % intervals over 30–100 trials (`14`) |
| **G18** | **new, fixed** | the Python we emitted used `/` for every division, but the prover reads `/` on two integers as whole-number division: a *proved* evenness test `n = 2 * (n / 2)` was always true when run (`16`, §7) |
| **G19** | **new, documented** | the specification text language gives `~` the *weakest* binding (`~(i = j) /\ rest` means `~((i = j) /\ rest)`), while the model-facing syntax's `!` binds tightly. Two of my own specifications were wrong for this reason; the mechanical spec check caught them |
| **G20** | **new, fixed** | Boolean variables could not be sent to Coq/Lean; they are now propositions (`15`) |
| **G21** | **new, fixed** | a timed-out `coqc` left its worker process running (found by looking at the machine's process list, not by a test) |


---

## 3. The prompt, audited (your professor's comment)

Your professor said the prompt is **wrong, not very detailed, and oriented to this particular problem.** I checked each part. (The full text the model sees is in Appendix A.)

### 3.1 "Oriented to this particular problem" — confirmed, in two places
* `llm/prompts.py:87-88` `[code]`: *"there are NO function calls: sqrt, max, abs, min are unavailable. A square root must be reached by refining to a loop, never by sqrt()."* — names the benchmark problem and tells the model the solution strategy.
* `llm/prompts.py:249,256,263,270` `[code]`: the format examples are `"x >= 0 && x <= N"` — the variable names and shape of the sqrt case.

Why it crept in: models kept answering `sqrt(N)` (§4.2 and the committed `gpt-oss-120b` log), so a hint was added. The *right* fix is general: state precisely what the expression language contains (and that nothing else exists), not a warning about one function.

### 3.2 "Not very detailed" — confirmed
| What the paper's prompt has `[paper]` | What ours has `[code]` |
|---|---|
| "all the details of the refinement rules" | a one-line blurb per law, no formal rule |
| the **condition** to be satisfied, as logical formulas of the *current* spec | only two laws; printed with a stray parameter header (see G3) |
| "The previous code … is not correct since …" | present in the parameter turn only; absent in the law-choice turn |
| the rule set as background knowledge + instruction tuning on worked examples | no examples at all, no general strategy for inventing invariants |

### 3.3 "Wrong" — concrete defects I can point at
1. Law-choice turn lacks the expression-syntax rules → models propose `sqrt(...)` assignments → a **whole wasted pair of LLM calls** per detour (in the live run, two impossible `assignment` attempts at N2 cost 4 calls, §6). `[code][log]`
2. The parameter prompt says "bounded below by 0" even when `FORMALLLM_STRICT_VARIANT=0`. It tells the model one thing while the engine checks another. `[code]`
3. The obligation text prints `I /\ ~G => (N:float)(e:float) := (((x * x) <= N) /\ …)` — the parameter header leaks into the formula. `[offline]`
4. Duplicate intro: *"We have decided to apply the law … to the following specification: You are a formal refinement agent. You have chosen…"*. `[offline]`
5. The prompt never says what the loop **body** will have to prove next (`[I ∧ G ∧ V=V₀, I ∧ …]`), so the model cannot design an invariant that the body can preserve. The paper does show this constraint. `[paper]`
6. No domain-independent guidance on *how to find* an invariant (e.g. "start from the postcondition and weaken it", "include every sign/range fact the body relies on"). `[code]`

### 3.4 What a paper-faithful, general prompt would contain (proposal, not yet built)
1. **Role + task** in two sentences.
2. **The languages**: L_spec expression grammar, the exact operator list, "no function calls of any kind", `x0` meaning, types (int vs float).
3. **The current specification** as `x:[P, Q]` plus the frame ("you may assign only to …").
4. **The law's rule and its *instantiated condition*** — generated by code from the law and the current spec, e.g. for assignment: *"find E such that `P ⇒ Q[x := E]`; here that means: `N ≥ 0 ∧ e > 0 ⇒ (E·E ≤ N ∧ N < (E+e)·(E+e))`"*. Same for every law. (This is Algorithm 1's `condition`.)
5. **Generic strategies**, never mentioning a benchmark: try `skip`/`assignment` first and say why they fail; for a postcondition that is a conjunction, keep one conjunct as invariant and negate the other for the guard; include in the invariant every fact the body relies on; etc.
6. **Failure feedback** in the paper's form: *"the previous parameters … are not correct since [counterexample]"*, plus, when a child failed, *that child's specification and its counterexamples*.
7. **A strict output schema.**
8. Optionally **2-3 worked examples from unrelated domains** (stand-in for the paper's instruction tuning) — kept out of the benchmark so they cannot leak answers.
9. **A unit test** that asserts no benchmark-specific token ("sqrt", "square", case ids) appears in any generated prompt, so the problem-orientation cannot silently return.

---

## 4. Offline experiment: how strict is "strict"? `[offline]`

Same paper spec (`x*x ≤ N ∧ N < (x+e)²`, frame `x`), one `initialised_iteration` step with the guard `N ≥ (x+e)²`, then `x := 0` and `x := x + e` as the two children. I varied what a model might plausibly write. Script: `…/runs/variant_sensitivity.py` (outside the repo).

| | Invariant | Variant | Strict (ours) | Paper-style (V < V₀ only) |
|---|---|---|---|---|
| A | `x*x ≤ N ∧ x ≥ 0` | `N − x*x` | ✅ accepted | ✅ accepted |
| B | `x*x ≤ N ∧ x ≥ 0` | `N − x` (the obvious linear one) | ❌ body rejected | ✅ accepted |
| C | `x*x ≤ N ∧ x ≥ 0` | `N − (x+e)*(x+e)` (read off the guard) | ❌ body rejected | ✅ accepted |
| D | `x*x ≤ N` (forgets `x ≥ 0`) | `N − x*x` | ❌ rejected | ❌ rejected |
| E | `x*x ≤ N ∧ x ≥ 0 ∧ x ≤ N+1` | `N + 1 − x` | ✅ accepted | ✅ accepted |
| F | `x*x ≤ N ∧ x ≥ 0 ∧ x ≤ N` | `N − x` | ❌ rejected | ❌ rejected |
| G | `x*x ≤ N` (no sign fact) | `N − x` (linear, always shrinks by `e`) | ❌ rejected | ✅ accepted |
| H | `x*x ≤ N` (no sign fact) | `N − (x+e)*(x+e)` (read off the guard) — **this is exactly the paper's Fig. 2** | ❌ rejected | ❌ rejected |

**Reading it:** the strict rule accepts 2 of these 8 plausible answers; the relaxed rule (variant must only decrease) accepts 5 of 8. Rows B and C are *natural* answers and the strict rule rejects them for a reason unrelated to the loop body's correctness: `0 ≤ N − x` fails when `N < 1` (e.g. `N = 0.25`, `x = 0.5`). Row D is a **real** bug (missing `x ≥ 0`) and is rightly rejected in both modes. Row F is also a real bug: `x ≤ N` is false for `N < 1`.

### 4.0 The paper's own Fig. 2, replayed exactly `[offline]` — the most important result in this file
I read the figure (see `11`, §5) and replayed its four steps against our engine: sequential with middle `x*x ≤ N`; `x := 0`; iteration with guard `N ≥ (x+e)*(x+e)` and variant `N − (x+e)*(x+e)`; body `x := x + e`.

| Step | Strict | Relaxed |
|---|---|---|
| sequential, middle `x*x ≤ N` | ✅ | ✅ |
| `x := 0` | ✅ | ✅ |
| iteration (exit obligation `I ∧ ¬G ⇒ Q`) | ✅ | ✅ |
| body `x := x + e` | ❌ **rejected** | ❌ **rejected** |

Counterexample from the engine, in both modes: **`x = −3, e = 1, N = 10`**. Check by hand: `x² = 9 ≤ 10` and `(x+e)² = 4 ≤ 10` hold; after `x = −2` the variant `N − (x+e)²` becomes `10 − 1 = 9`, up from `10 − 4 = 6`. The invariant `x² ≤ N` as printed allows negative `x`.
If the body is only required to **preserve the invariant** (partial correctness — no variant obligation) the same step is ✅ accepted.

**Consequence:** with a total-correctness check on the loop variant, our engine *cannot* reproduce the paper's headline example as printed. Either the paper's ATP step checks only the invariant (consistent with its own remarks "partially correct", §3.1, and §11.3), or the printed invariant omits `x ≥ 0`. This is a question for Dr. Hou, not something I should settle by guessing.

> Taken together, the table above and §4.0 show our default is *harsher than the paper's* on plausible answers. **They do not show that strictness is why runs fail** — the repo's own end-to-end ablation says otherwise:

### 4.1 The existing strict-vs-lenient ablation (end to end, paper's sqrt, refinement arm) `[log]`
Recomputed by me from `benchmarks/results/results_strict.jsonl` and `results_lenient.jsonl` (2 trials per model, `C5-sqrt-paper`):

| Model | Strict: SUCCESS | Lenient (paper-style): SUCCESS | Calls in the successful run (strict → lenient) |
|---|---|---|---|
| gpt-oss-120b | 1 of 2 | 1 of 2 | 9 → **4** |
| llama3.1, llama3.1-wide, ornith, ornith-think, qwen3.5-nothink, qwen3.5-think, qwen3-coder-next | 0 | 0 | — |

**Honest reading:** switching the termination rule did **not** change how many runs succeeded (1 vs 1, tiny sample), but it made the one successful run more than twice as cheap (4 calls instead of 9). Every other model fails in *both* modes, so strictness is not what stops them. For `llama3.1` I inspected the traces and the cause is upstream — unparsable expressions and choosing `assignment` with `sqrt` (§4.2); for the other models I have **not** inspected the traces `[hypothesis: similar]`. So D1 is mainly an **efficiency and fidelity** decision, not the cure for sqrt.

### 4.2 What small models actually do wrong (from `results.jsonl`, `llama3.1`, C5, 3 trials, all EXHAUSTED) `[log]`
The first trial: 9 LLM calls → 5 attempts: 3 `ERROR` (expressions the parser rejected: unexpected `(`, `:` and `.` tokens) and 2 `REJECTED`; laws tried: `assignment` ×3 (with `sqrt(N)` and `x + e`), `strengthen_post` ×2 (re-stating the postcondition with `x0`). Never reached `sequential`/`initialised_iteration`. These are **syntax and law-choice failures**, exactly what a precise, example-rich prompt (and the paper's instruction tuning) is meant to prevent.

### 4.3 Measurement validity (a gap in its own right) — G15
* Several cells have **n = 1 or 2**; one run flips a cell from 0 % to 50 %.
* Infrastructure failures are **counted as model failures**: e.g. `results_strict_gpt.jsonl` and `results_lenient_gpt.jsonl` hold `transport_error: "Failed to reach https://…ngrok…"` recorded as `status: no_function`, and `results_strict_refinement_gpt120b.jsonl` has `"No credentials for …"` errors recorded as failed trials. A tunnel hiccup or a missing password therefore reads as "the model cannot do it".
* **Budget stops are mislabelled `EXHAUSTED`** (G16). In the committed data this looks small: using each configuration's largest observed call count as a proxy for its budget, 4 of 68 `EXHAUSTED` records in `results.jsonl` (excluding `qwen3.5-think`, whose largest observed call count of 4 says nothing about its budget) and 5 of 29 in the three study files sit exactly at the limit; the live run shows the effect is total once it happens.
* Proposal: retry transient errors, exclude them from denominators and report them separately; use ≥ 5 trials per cell; report counts, not percentages.

---

## 5. Efficiency findings `[offline][log]`

| Quantity | Value | Source |
|---|---|---|
| Z3 time, full sqrt derivation (3 steps) | **0.018 s** | `[offline]` |
| Minimum LLM calls for sqrt in our two-turn design | 6 (root law+params, `init` law+params, `body` law+params) | `[code]` |
| LLM calls actually used by `gpt-oss-120b` (committed log) | 10 (4 extra: a wrong `assignment` detour, then `strengthen_post` to add `x ≥ 0`) | `[log]` |
| Wall time, refinement vs direct generation (same model) | 675 s vs 193 s | `[log]` |
| Average latency per call | ≈ 67 s (120B model behind a tunnel, reasoning on) | `[log]` |

So efficiency work should target **number and size of LLM calls**, not the solver. Ideas aligned with the paper (all optional, each needs your OK):
* shorten the path by supplying the *instantiated condition* up front (fewer detours);
* derive the guard (and variant) from the postcondition shape, as §10.1 describes, so the LLM writes one formula instead of three;
* never spend a turn on a law the syntax makes impossible;
* refine independent siblings (`init`, `body`) concurrently — the paper notes modular verification "facilitates parallel verification" (§7.2).

---

## 6. Live run (`gpt-oss-120b`, case C5, current prompts) `[live]`

*Started 20:33 IST on 2 Oct 2026 with `--budget 40 --max-retries 4`, temperature 0.2; output went to a temp folder, not into the repo's results file. Parameters below are copied from the model's JSON replies in the run log.*

### 6.1 What the model proposed, node by node

| Node (depth) | Law | Parameters proposed | Outcome |
|---|---|---|---|
| N0 (0) | `sequential` | `intermediate: x*x <= N` | accepted → N1, N2 |
| N1 (1) | `assignment` | `x := 0` | accepted ✅ |
| N2 (1), try 1 | `assignment` | *(empty parameters)* | error: "requires 'variable' and 'expr'" |
| N2 (1), try 2 | `assignment` | `x := x` | rejected: counterexample `N=2, e=1, x=0` |
| N2 (1), try 3 | `initialised_iteration` | invariant `x*x <= N`, guard `(x+e)*(x+e) <= N`, variant `N − (x+e)*(x+e)` | accepted → N3, N4 |
| N3 (2) | `skip` | — | accepted ✅ |
| N4 (2) — the loop **body** | `sequential` | middle: `N>=0 && e>0 && x*x<=N && (x+e)*(x+e)<=N && N−(x+e)*(x+e) <= N0−(x0+e0)*(x0+e0)` | accepted → N5 … |
| N5 (3) | `strengthen_post` | same conjunction **plus `x >= 0`** | accepted → N7 … |
| N7 (4) | `weaken_pre` | `N >= 0 && e > 0` | accepted → N8 |
| N8 (5) | `weaken_pre` | `N >= 0` | accepted → N9 |
| N9 (6) | `assignment` / `weaken_pre` / `initialised_iteration` / `alternation` | `{}`; `N >= -1`; a loop whose invariant contains `x >= 0` but with guard `0 > 1`; guard `e > 0` | 4 attempts (12 calls), all failing |
| N10 (6), try 1 | `initialised_iteration` | **`I = N>=0 && e>0 && x>=0 && x*x<=N`, `G = (x+e)*(x+e)<=N`, `V = N − x*x`** — the fully correct loop (row A of §4) — but sent under the keys **`"I"`, `"G"`, `"V"`** | error: *"initialised_iteration requires guard and variant and invariant"* — the engine never saw the answer |
| N10 (6), tries 2-3 | `weaken_pre`, `strengthen_post` | `true` / `N >= -1`; a long conjunction ending `… && x*x <= N − e*e` | failing; try 4 and all root retries had **no budget left** |

### 6.2 What this shows `[live]`
1. **The model found the paper's Fig. 2 decomposition on its own**, in the first three steps: middle `x² ≤ N`; `x := 0`; invariant `x² ≤ N`, guard `(x+e)² ≤ N`, variant `N − (x+e)²`. Law selection and parameter synthesis for the *top* of the tree were not the problem in this run.
2. **The failure is then a credit-assignment failure.** The body `x := x + e` cannot be verified because the *parent's* invariant lacks `x ≥ 0`. (The model never actually submitted `x := x + e` at N4; but N4's specification depends only on the parent's invariant, guard and variant, so it is identical to the one in my §4.0 replay, where that step fails with `x = −3, e = 1, N = 10`.) The model never learns that: the body node is searched on its own, and the model tries to repair it **locally** with structural laws (`sequential` → `strengthen_post` → `weaken_pre` → `weaken_pre` → …). It even *notices* `x ≥ 0` (at N5) — but adds it to a sub-goal that cannot establish it, because the precondition says nothing about the sign of `x`. Six levels deep, the depth limit forces terminal laws and everything fails.
3. **The parent gets no useful feedback.** When a subtree is exhausted, the parent's history says only `"Child node 'N4' exhausted all options. Blacklisted: […]"` (gap G6): no child spec, no counterexample. The paper's Algorithm 1 instead *falls back to the previous step with the failure details* (G5/G7).
4. **Cost:** of the **40** LLM calls, **27 (68 %)** were spent in the loop-body subtree (N4 and below: 2+2+2+2+12+7) that could never succeed, and 5 more on N2's two impossible `assignment` attempts. Only the first 4 calls (N0, N1), the successful N2 step and N3 were useful. A working path needs **6 to 10** calls (6 if the root uses `initialised_iteration` directly; 10 for the decomposition above).
5. **The body spec is hard to read** (gap in §3.3): it is displayed with `N0`, `x0`, `e0` — "previous-state" copies even of constants that never change — and with ≈ 6 levels of parentheses. A clearer rendering would introduce one named constant for the variant's starting value.
6. **Correction to an earlier note of mine:** the model *considered* `sqrt(N)` in its reasoning at the root (spending reasoning tokens on it) but its reply was `sequential`. The repeated `sqrt(...)` assignments are documented in the committed `gpt-oss-120b` log, not in this run.

7. **A format-robustness failure threw away a correct answer.** At N10 the model sent `{"I": …, "G": …, "V": …}`. Our prompt's schema example reads `{"invariant": "I", "guard": "G", "variant": "V"}`, i.e. the letters `I`, `G`, `V` appear as *placeholders*, and the model echoed them as *keys*. The parameter parser accepts only the exact key names. Two cheap, general fixes: show the schema with a realistic example from an unrelated problem, and accept obvious aliases. (New gap G17.)
8. **The budget signal is swallowed (a real bug, new gap G16).** `refine_node` wraps each step in `except Exception`, and `BudgetExhausted` is an `Exception`. Of the 34 error messages recorded in this run, **23 are literally "LLM call budget of 40 exhausted"**: the refiner logged each as a failed *attempt*, kept looping up through the tree, and the run ended as `EXHAUSTED` ("Blacklisted laws: []") instead of `BUDGET`. The result file therefore misreports *why* it stopped, and the graph is padded with fake attempts.

### 6.3 Result
| | |
|---|---|
| Outcome recorded | **`EXHAUSTED`** (really: the 40-call budget ran out — see item 8) |
| LLM calls | 40 (budget 40) |
| Wall time | **1,668 s (27.8 min)**; mean 41.7 s per call, essentially all of it LLM time (Z3 ≈ 0.02 s) |
| Tokens reported by the provider | 73,268 prompt; 8,171 output (may not include hidden reasoning tokens) |
| Graph | 11 nodes (2 refined, 8 failed, 1 open); 50 attempts: 27 `error` (23 of them the budget message), 10 `rejected`, 7 `aborted`, 2 `accepted`, 4 `pending` |
| Laws proposed | `weaken_pre` 14, `sequential` 10, `strengthen_post` 8, `assignment` 8, `initialised_iteration` 7, `alternation` 2, `skip` 1 |
| Laws accepted | `assignment` 1, `skip` 1 (plus the accepted structural steps that led nowhere) |
| Final program | none |

**Sample size: 1 trial.** This is a diagnosis of *how* a run fails, not a success rate. The committed log shows the same model finishing this case once (10 calls, 675 s); it is a coin flip with a very expensive losing side.

**What would have rescued this run, in order of cheapness:** (1) accept `I/G/V` as aliases — the N10 answer was correct; (2) report the body's counterexample (`x = −3 …`) to the node that chose the invariant, so N2 re-proposes with `x ≥ 0` after its *first* failure instead of after 27 calls; (3) don't let structural laws (`sequential`/`weaken_pre`/`strengthen_post`) loop on a spec they cannot change — the progress guard compares text, and a re-worded conjunction counts as "progress".

---

## 7. Decisions I need from you (nothing is changed until you answer)

| # | Decision | Options | My recommendation |
|---|---|---|---|
| **D0** | What does "follow the paper's result" mean for us? | (a) reproduce the *mechanism* on sqrt (Figs. 2/3/9) with a strong model; (b) also approximate Table 7 (steps + proof time on classic problems); (c) also Table 6 (HumanEval-scale) | (a) now, (b) next. (c) needs 164 formal specs — a separate project. |
| **D1** | Termination policy (three possible guarantee levels: **total** = `0 ≤ V < V₀`; **decreasing** = `V < V₀` only; **partial** = body just preserves the invariant, termination not checked) | (a) keep strict only; (b) relaxed only; (c) *graded*: try total → decreasing → partial, accept the strongest that verifies, and **record the level** in the trace and in every results table | **(c)** — it is the only option that can reproduce Fig. 2 (partial) while still reporting when a stronger guarantee was achieved. Ask Dr. Hou which level Fig. 2 intends (Q1 below). |
| **Q1** | *Question for Dr. Hou* | "In Fig. 2, is the loop-body check `x = x + e` a proof of variant decrease, or only invariant preservation? With invariant `x² ≤ N` the decrease fails for negative x (e.g. x = −3, e = 1, N = 10)." | — |
| **D2** | Loop parameters | keep (I, G, V) / make V optional and derive it from the guard | derive V (paper §10.1) |
| **D3** | Prompt redesign scope | §3.4 items 1-7 / plus worked examples / plus a retrieval library | items 1-7 + 2-3 examples now; library later |
| **D4** | Retry policy | keep / follow Algorithm 1 (fall back after >5 failures, never blacklist a law because its *parameters* were wrong) | follow Algorithm 1 |
| **D5** | Child-failure feedback | keep / pass child spec + counterexamples to the parent | pass them |
| **D6** | Missing laws | none / assertion iteration (6.7) first / also 6.3, 6.4, 6.8 + `assert` in L_pl | 6.7 first |
| **D7** | Lean/Coq | later / now | ~~later~~ **RESOLVED (you: "then automated Lean and Coq")** — built and measured, see `15`. Z3 searches; Coq and Lean re-check every finished derivation; `z3+lean` lets Lean prove what Z3 leaves `unknown`. |
| **D8** | Model for the main experiments | `gpt-oss-120b` (hosted, strongest we have) with local models as a secondary arm | yes |
| **D9** | Fix the two pure bugs now? (G16: budget stop swallowed → mislabelled results; G17: accept `I/G/V`-style aliases and fix the schema example). They do not depend on any paper decision. | now / wait | **now** — small, tested, and they stop results being mislabelled |

---

## Appendix A — what the model sees today (root node of the paper's sqrt spec)

**Turn 1 — law selection** (2,467 characters; note: no syntax rules, no history):

```
You are a formal refinement agent. Your task is to select a refinement law to apply to the following specification.

Specification:
Precondition: (N:float)(e:float) := ((N >= 0) /\ (e > 0))
Postcondition: (N:float)(e:float) := (((x * x) <= N) /\ (N < ((x + e) * (x + e))))

You may ONLY assign to: x.
Every other name is fixed and must not be assigned; whatever the precondition says about those names stays true throughout.

Available Laws:
- "assignment": parameters: {"variable": "x", "expr": "E"} -- refines to the assignment x := E.
- "skip": no parameters -- valid only when P already implies Q.
- "initialized_skip": no parameters -- skip, assuming every variant keeps its previous-state value.
- "sequential": parameters: {"intermediate": "R"} -- splits into [P,R] ; [R,Q]. Note: R must be a BARE boolean expression …
- "flexible_sequential": parameters: {"pre1": "A", "post1": "B", "pre2": "C", "post2": "D"} -- splits into [A,B] ; [C,D], requiring P => A, B => C and D => Q. …
- "alternation": parameters: {"guard": "G"} -- splits into if G then [P/\G, Q] else [P/\~G, Q].
- "iteration": parameters: {"guard": "G", "variant": "V"} -- builds while G do (body). Valid ONLY when the precondition is already the loop invariant. V is an expression that strictly decreases each iteration.
- "initialised_iteration": parameters: {"invariant": "I", "guard": "G", "variant": "V"} -- builds x:[P,I] ; while G do (body). I is the loop invariant: … Supplying I lets one step introduce both the initialisation and the loop.
- "strengthen_post": parameters: {"intermediate_post": "R"} -- replaces Q by a STRICTLY STRONGER R (R => Q). …
- "weaken_pre": parameters: {"intermediate_pre": "R"} -- replaces P by a STRICTLY WEAKER R (P => R). …

Every step must make progress: never choose a law that will reproduce a sub-specification identical to the one above.

Respond ONLY with valid JSON of the form:
{ "law": "<name>", "rationale": "<step-by-step reasoning for choosing the law>" }
Do not include markdown formatting or explanations outside the JSON.
```

**Turn 2 — parameters for `initialised_iteration`** (2,115 characters), the part after the specification:

```
Law: "initialised_iteration": parameters: {"invariant": "I", "guard": "G", "variant": "V"} -- builds x:[P,I] ; while G do (body). …

Obligations for initialised_iteration:
1. The invariant (I) must be established by the initialization from the Precondition.
2. The invariant and negated guard must imply the Postcondition: I /\ ~G => (N:float)(e:float) := (((x * x) <= N) /\ (N < ((x + e) * (x + e))))
3. The variant (V) must be strictly decreasing and bounded below by 0: 0 <= V

Expression syntax (this is NOT Python):
- conjunction: write &&    disjunction: write ||    negation: write !
  …
- there are NO function calls: sqrt, max, abs, min are unavailable.
  A square root must be reached by refining to a loop, never by sqrt().
```

(Note the stray header in obligation 2, the hard-coded "bounded below by 0", and the `sqrt` sentence.)

---

## Check yourself
1. Which parameters does the paper's Table 5 say the LLM provides for iteration, and which does our `initialised_iteration` demand? *(paper: I, G; ours: I, G and V.)*
2. Why is "Z3 vs Coq" not the explanation for the sqrt failures? *(Z3 decides all three sqrt obligations in 0.018 s; the failures are in what the LLM proposes and in how much we reject.)*
3. Name two things in our prompt that are specific to one benchmark problem. *(The `sqrt` sentence; the `x >= 0 && x <= N` examples.)*
4. In the offline table, why does variant `N − x` fail under the strict rule but pass under the paper's? *(Strict adds `0 ≤ V`, which is false when `N < 1`.)*
5. What does the paper's Algorithm 1 do after more than 5 failures on one specification? *(Falls back to the previous step and tries another law.)*
6. Why does the paper's Fig. 2 loop body fail our check, and what weaker check does it pass? *(The invariant `x² ≤ N` allows negative `x`, for which `x + e` can make the variant grow; it passes if the body only has to preserve the invariant — partial correctness.)*
7. Name the three guarantee levels in decision D1. *(Total `0 ≤ V < V₀`; decreasing `V < V₀`; partial — invariant only.)*
