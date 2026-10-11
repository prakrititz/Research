# 13 — The General Prompt and the Hardened Engine

> **Why this file exists.** Your professor said the prompt was *wrong*, *not very detailed* and *oriented towards one problem* (the square root). In `12` I audited it and agreed on all three counts. This file describes what was rebuilt, how generality is now **enforced by tests**, and the engine bugs found on the way. Results (how often it works) are in `14`.
>
> **Evidence tags:** `[ran]` I ran it · `[read]` read in code · `[test]` a unit test enforces it.
> Read `11` and `12` first.

---

## 1. Before and after, at a glance

| | Before | Now |
|---|---|---|
| Prompt mentions a benchmark problem | yes (`sqrt` hint, sqrt-shaped examples) | **no — enforced by a test** `[test]` |
| What each law is told | a one-line blurb | rule, parameters, *when to use*, and the **proof condition instantiated for this specification** |
| Law-choice turn knows the expression syntax | **no** (models proposed `sqrt(N)`) | yes |
| How a specification is shown | `((((N >= 0) /\ (e > 0)) /\ ...` | bullet list, one fact per line |
| The loop variant's starting value | `N0 - ((x0 + e0) * (x0 + e0))` | the paper's `V0`, a real named constant |
| Why a proof failed | "values: N=4, N0=2, x0=0, e0=0 ..." | which **part of the goal** is false, with the value of `V0` |
| What a parent hears when its child fails | "Child node N4 exhausted all options" | the child's specification, the failed proof, its counterexample — and, when the assist can tell, **which fact to add to which of the parent's own parameters** (§5.1) |
| Advice after a failed proof | one sentence for every law ("strengthen the invariant") | specific to the obligation (a set-up failure says *weaken*, an assignment failure says *change E*) `[test]` |
| Reply keys `I`/`G`/`V` | correct answer **discarded** | accepted |
| Examples shown to the model | none | one correct worked example per law, from a problem **not** in the benchmark `[test]` |

---

## 2. Anatomy of a prompt `[read]`

Every prompt is assembled from the same ordered sections (`FormalLLM/llm/prompts.py`, `law_cards.py`):

1. **Role** — "an expert in Morgan's refinement calculus … every step is checked by a theorem prover."
2. **Notation** — what `x : [P, Q]` means, what the frame is, that constants never change.
3. **Expression language** — exactly which operators exist; "there are NO function calls of any kind … no if-then-else"; `v0` means the earlier value. (This replaced the sentence about square roots with a *definition of the language*, which is the general fix.)
4. **The specification**, rendered readably:
   ```
   Frame (the only names the program may assign): x
   Constants (never assigned): N:float, e:float
   Precondition P (may be assumed on entry):
     - N >= 0
     - e > 0
   Postcondition Q (must hold on exit):
     - x * x <= N
     - N < (x + e) * (x + e)
   ```
5. **System check** — a fact the prover settles *now* so the model need not guess: *"P does NOT imply Q, so skip is not valid (for example N = 2, e = 1, x = 0 satisfy P but not Q)."*
6. **The laws** — one card each (§3).
7. **A general method** — a numbered strategy and a **loop recipe** (§4), written without reference to any problem.
8. **Reply format** — one JSON object, with the exact keys for the chosen law.
9. **Feedback**, when there is any — what already failed, why, and how to read a rejection.

The same sections feed all three modes: the two-call mode of the paper's Algorithm 1 (law, then parameters) and a one-call mode.

---

## 3. A law card `[read]`

Taking `initialised_iteration` as the example (rewritten by the program for the current specification):

```
- initialised_iteration: set-up step followed by a loop with your own invariant
    rule: x : [P, Q]  refines to  x : [P, I] ; while G do x : [I and G and V = V0, I and V < V0]
          provided  I and not G implies Q
    parameters: "invariant" = I ...; "guard" = G ...; "variant" = V ...
    use when: the postcondition is reached by repeating a step: search, accumulate, scan, approach a bound.
    for this specification:
      The system checks the exit condition: I and not G implies Q.
      Then these specifications are refined next:
        set-up       [ P , I ]
        loop body    [ I and G and V = V0 ,  I and 0 <= V and V < V0 ]   (V0 is the value of V when the body starts)
        facts about constants added to I automatically: N >= 0; e > 0
```
This is the paper's own idea (Algorithm 1: the system derives the *condition* from the law and the specification, then shows it to the LLM; its Fig. 6 draws the "Constraints" box going **into** the LLM). The old prompts did it for two laws out of ten and printed a stray parameter header inside the formula.

---

## 4. The general method and the loop recipe `[read]`

The strategy text and the loop recipe are *domain-independent*. The recipe, in full:

1. Look at Q. When it is a conjunction, one part A can usually be made true by a simple initial assignment, while another part B is what the loop must achieve.
2. **Invariant I:** start from A and add every fact the loop body relies on, for instance the range or sign of each variable the body changes and the relations between loop variables and constants.
3. **Guard G:** the negation of B, so that when the loop stops, Q holds.
4. **Variant V:** an expression measuring how far the state is from satisfying B; (the exact rule the engine checks is stated: *"V must stay ≥ 0 and be strictly smaller"* or just *"strictly smaller"*, depending on the setting — the old prompt always said the first even when the engine checked the second).
5. The loop body is then usually a single assignment (or two in sequence).

Why this matters for the square root: item 2 is what makes a model write `x >= 0` in the invariant. That sign fact is *exactly* what the paper's Fig. 2 omits and what our prover needs (`12`, §4.0). The recipe never mentions the square root; it says "the range or sign of each variable the body changes".

---

## 5. Feedback: what the model hears after a failure `[ran]`

**Before** (a rejection):
```
Counterexample (...): N = 4, N0 = 2, e = 1, e0 = 0, x = -2, x0 = 0
```
**Now:**
```
The obligation that failed: the assignment must establish the postcondition: P => Q[x := E]
  assuming:      - N >= 0   - e > 0   - x * x <= N   - N >= (x + e) * (x + e)   - N - x * x = V0
  must show:     - N >= 0   - e > 0   - (x + e) * (x + e) <= N   - 0 <= N - (x + e) * (x + e)   - N - (x + e) * (x + e) < V0
Counterexample (these values satisfy the assumptions but falsify the goal): N = 4, e = 1, x = -2, V0 = 0
For these values the following part of the goal is false:
    - N - (x + e) * (x + e) < V0
```
The model can now see that the *decrease* requirement is what breaks, and for a **negative** `x`.

**When a subtree fails, its parent hears** (`FormalLLM/agent/refiner.py`, `_failure_digest`):
```
Sub-specification 'body' (N2)  [ ... ] could not be refined. The first proof that failed there was law 'assignment' with variable = x; expr = x + e:
    Counterexample (...): N = 4, e = 1, x = -2, V0 = 0
    For these values the following part of the goal is false:
      - N - (x + e) * (x + e) < V0
  Such a failure usually comes from the parameters chosen at THIS step (for example an invariant or intermediate assertion that is too weak or too strong for that sub-specification), not from the sub-specification itself.
```
The point is **credit assignment**: the child is blamed on the choice that made it unprovable. In the earlier live run, 27 of 40 LLM calls were burned because this information was missing (`12`, §6).

### 5.1 Second round of fixes: telling the *right step* what is wrong `[ran][test]`

The first version of this feedback still failed about one run in four, and reading the failed transcripts (`14`, §4) showed *why*: the information was there, but it was addressed to the wrong step. Three faults, each now fixed and pinned by a test in `FormalLLM/tests/test_repair.py`:

| # | Fault found in a failed run | Fix |
|---|---|---|
| 1 | The loop body `x := x + e` was refuted at `x = -3`. The message ended "…strengthen the invariant…" — **but the body node cannot change the invariant; its parent chose it.** The model answered with nested loops instead, and 16 LLM calls disappeared. | Each proof obligation now carries its own advice (`ProofObligation.advice`), written by the law that created it. The generic sentence was wrong for several obligations (for the *set-up check* it said "strengthen" when the invariant needed *weakening*). |
| 2 | When that subtree finally failed, the parent was shown **the first rejection recorded at the child — which was one of the system's own quick tests of a different node**, not the model's loop. The parent blamed the wrong choice (it changed an innocent intermediate assertion to `true`). | `_failure_digest` now ignores the system's own probes when looking for the model's failed proof, and follows an accepted-but-failed step down to the part that actually failed. |
| 3 | When a subtree used up its allowance of calls (16), the **node that owned the allowance was declared failed outright**, so it never got to repair its own loop. | The allowance belongs to a *step*: when it runs out, that step is aborted with an explanation and the node proposes again with a fresh allowance. |

On top of that, one new piece of *diagnosis* (still part of the optional assist, §8):

**Missing-fact diagnosis (`LeafSolver.missing_fact_for`).** When the obvious one-line body (`x := x + e`) is refuted, the system asks the prover one more question for each of a small, generic family of facts about the variables (`x >= 0`, `x > 0`, `x <= N`, …): *"would the same step be valid if the precondition also guaranteed this?"* The first fact for which the answer is yes (and which does not make the precondition contradictory) is reported. For the square-root loop with the invariant of the paper's Fig. 2 it says:

```
Sub-specification 'body' (N4)  [ … ]  could not be refined. Its simplest candidate, x := x + e, is refuted:
    Counterexample (these values satisfy the assumptions but falsify the goal): N = 10, V0 = 6, e = 1, x = -3
    For these values the following part of the goal is false:
      - N - (x + e + e) * (x + e + e) < V0
  The same step would be valid if the precondition of this sub-specification also guaranteed x >= 0.
  That precondition is built from the loop invariant of the step above: add x >= 0 to the invariant
  (it must then also hold after the set-up step).
```

and the body node **returns to its parent at once, spending no LLM call**. The parent — the node that chose the invariant — then re-proposes with this message in front of it. Nothing here mentions square roots: the family of facts is generated from the names in the specification, and `tests/test_repair.py` checks that no fact is invented where none would help (at the root, or at the second half of a `sequential`) and that a fact which would make the precondition contradictory is never offered.

---

## 6. `V0` is now a real name `[read][test]`

The loop laws used to state "the variant starts at V0" as `V = V0'`, where `V0'` was the variant with every variable renamed to its previous-state copy: `N - x*x` became `N0 - x0*x0`. That is logically equivalent but it shows the model copies of constants that never change (`N0`, `e0`), and a model that read `V0` in the displayed specification and wrote it in its own intermediate assertion referred to something the engine did not know.

Now the laws introduce a fresh constant `V0` (`V1`, … if an enclosing loop already used it), exactly as the paper's Lemma 2.7 writes it. What the model reads is what the prover uses; `tests/test_prompts_general.py` even shows a worked loop whose body uses `V0` in an intermediate assertion and is accepted.

---

## 7. Bugs found and fixed on the way

| Bug | Effect | Fix | Test |
|---|---|---|---|
| The budget stop was caught as an ordinary failure | a run that ran out of calls was reported "exhausted all options" and padded with 23 fake attempts | `LLMBudgetExhausted` propagates | `test_robustness.py` |
| Parameter keys had to match exactly | a **correct** loop sent as `{"I":…, "G":…, "V":…}` was discarded | aliases + bare objects + a precise error for unknown keys | `test_robustness.py` |
| `!(x < 0) && y > 1` parsed as `~((x<0) /\ (y>1))` | the model's meaning changed silently ("not both") | each negation binds to its own operand | `test_robustness.py` |
| Spec-reshaping steps could be chained (`strengthen_post → weaken_pre → weaken_pre …`) | 27 of 40 calls wasted below a loop body | a reshaping step may not follow a reshaping step | `test_robustness.py` |
| A failed proposal could be repeated verbatim | wasted proofs and calls | rejected without a proof, with a reminder | `test_robustness.py` |
| Retry policy blacklisted a law after 2 failed parameter tries | harsher than the paper (fall back after more than 5 failures) | 3 tries | existing fallback tests |
| History printed parameters as `BinaryOp(left=Variable(...)...)` | noise | printed as formulas | `test_robustness.py` |

---

## 8. The optional "leaf assist" — flagged, off by default

`FormalLLM/agent/assist.py`. After a loop is chosen, most remaining nodes are not creative: the set-up is `x := 0`, the body is `x := x + e`. With the assist **on**, a node that `skip` or **one short assignment built from the specification's own names** can settle is closed by the prover with no LLM call. Every candidate goes through the same engine, laws and prover as a model's proposal. The **creative choices — which law, invariant, guard, variant — stay with the model.**

It does four things, all through the same prover:

1. **Closes one-line leaves** (`skip`, or one assignment from the specification's own names) with no LLM call.
2. **Diagnoses a refuted leaf** (§5.1): if the obvious update fails only for want of a fact the precondition lacks, the node returns to its parent with that fact named.
3. **Solves an equation of the postcondition for a variable** (`solved_for`). `q * d + r = n` solved for `r` gives `r := n - q * d`. Only `+`, `-` and negation are undone; a product is never "divided out", and only an equation in which the variable occurs once is used. The result is just one more candidate, tried after the short families, so every existing derivation is unchanged.
4. **Closes a set-up or a loop body that changes two variables** (`solve_pair`): two assignments in a row, `a := E1 ; b := E2`. The search runs backwards: pick `E2` (from the short candidates, or from an equation), take the middle assertion to be the weakest precondition `Q[b := E2]`, so the second part holds by construction, then search `E1` among the short candidates. A few cheap checks prune the search (for example, a conjunct of the middle assertion that does not mention `a` must already follow from the precondition), and it stops after four seconds. It applies only to non-root nodes whose frame has at least two variables.

All four are *proposals*: each assignment is accepted only if the engine's prover proves `P => Q[x := E]`, exactly as for a model's proposal. The split itself carries no proof obligation, and the engine's extra feasibility check on it is skipped because a stronger fact is already in hand (both halves are closed by proved assignments). The refiner records an assist-made split like any other step (two child nodes, each closed by an assignment), so the program is reconstructed and the Coq/Lean certificate covers it the normal way (`test_assist_pairs.py` checks the obligations that reach the certificate).

**Guesses are checked by Z3 alone**, even when the run's backend is Lean or Coq (`LeafSolver.screen`): the assist tries hundreds of tiny candidates per stuck step, and a proof assistant at about 10 s each would make a run a hundred times slower. The model's own proposals, and the final re-application of an assist-made split, still go through the backend the run was configured with, so what is accepted is checked exactly as before (`test_assist_pairs.py` has a backend that raises if it is ever asked about a guess).

It is **not in the paper**, so it is off by default and reported as its own arm (`14`). Its effect on the square root: from "the model has to rediscover `x := 0` and `x := x + e`, and sometimes answers with another loop" to "two LLM calls for the whole derivation" (three when the first invariant needs repairing).

**Why 3 and 4 exist (measured, `14` §5e).** On integer division (`Frame: q, r`) the model chose the textbook loop (invariant `q*d + r = n && r >= 0`, guard `r >= d`, variant `r`) almost every time, but the set-up `r := n ; q := 0` and the body `r := r - d ; q := q + 1` each need *two* assignments, which the one-line helper could not close. The model, asked next, guessed middle assertions that could not be finished, and 19 of 20 trials ran out of their 30 calls (the other finished by a different route after 26). With 3 and 4 the model's only job is the loop; the example derivation is `r = n; q = 0; while r >= d: r = r - d; q = q + 1`.

---

## 9. How generality is enforced `[test]` (`FormalLLM/tests/test_prompts_general.py`)

1. Every prompt, built for a *neutral* specification, is scanned for benchmark vocabulary (`sqrt`, `square`, `root`, `quotient`, `remainder`, `division`, `factorial`, `absolute`, `counting` …).
2. For **each of the 13 benchmark specifications**, the *teaching text* of the prompt (everything except the specification itself and the lines computed from it) must be **identical** to the neutral one. So no problem gets different instructions.
3. Every worked example is checked **not** to be a benchmark specification.
4. Every worked example is checked to be **correct**: the real engine accepts it, its reply parses with the real parser, and the loop example's body can really be finished with assignments.

If anyone ever re-introduces a problem-specific hint, one of these fails.

---

## 10. What is not done

* **The prompts have not been tuned on a second model family.** They were developed against `gpt-oss-120b`. One other hosted model (`qwen3-coder-next`) is measured in `14`; the smaller local models (llama3.1, qwen3.5, ornith) mostly fail on syntax and are not re-measured.
* **The strict/relaxed termination choice is still open** (decision D1 in `12`): the results in `14` are reported under both. A note on what each *proves*: over **integers** the strict rule (`0 ≤ V < V0`) implies the loop terminates; the relaxed rule (`V < V0`) does not (the variant could go on decreasing below zero). Over **real numbers** neither does (a variant can decrease forever without reaching a bound, e.g. by halving); the square root terminates because `x` grows by the fixed amount `e`, a fact neither rule checks. So "verified" here means *partial correctness plus the variant condition* — which is also all that the variant conditions of the paper's loop lemmas (6.6 and 6.7) state — not a full termination proof for real-valued loops.
* **The feasibility check and the name check are refusals, not repairs.** They tell the model what is wrong at once; they do not choose a better invariant.
* **Worked examples are a stand-in for the paper's instruction tuning**, not the same thing; the paper fine-tuned GPT-4 on Morgan's examples.
* The prompt is long (≈ 10,000 characters for the law-choice turn). That is fine at this scale; if a larger law set is added it should be trimmed to the relevant laws.

---

## Check yourself
1. Name two things in the *old* prompt that were specific to the square root. *(The `sqrt` sentence; the `x >= 0 && x <= N` format examples.)*
2. What does the "system check" line give the model, and why is it better than letting it guess? *(Whether `P` already implies `Q`, with example values, settled by the prover.)*
3. What is "credit assignment" and how does the parent now get it? *(Blaming the right decision; the parent is shown the child's specification, the first failed proof and the counterexample.)*
4. Why did `V0` change from a copy built with previous-state variables to a named constant? *(So the model's `V0` and the prover's `V0` are the same symbol, and nothing irrelevant like `N0` is displayed.)*
5. Why is the leaf assist reported as a separate arm instead of simply switched on? *(It is not part of the paper's pipeline, so its effect has to be measured, not assumed.)*
