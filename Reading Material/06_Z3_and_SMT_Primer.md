# 06 — Z3 and SMT, in Plain Words

> **Prerequisites:** `02_Formal_Methods_Primer.md` (especially §5, "what the machine actually checks").
> **Why this file matters most:** Z3 is the **only verifier this repository uses today** (`FormalLLM/verification/z3_backend.py`). If you understand this file, you understand how every refinement step is accepted or rejected.
>
> All Python snippets below were **actually run** (Z3 version 5.1.0 via the `z3` Python package on this machine). Outputs shown are the real ones. Install: `pip install z3-solver`.

---

## 1. What is a SAT/SMT solver?

**SAT** = *Boolean satisfiability.* Given a formula built from true/false variables, is there an assignment making it true?

**SMT** = *Satisfiability Modulo Theories.* Same question, but formulas may include integers, reals, arrays… ("theories") with their usual meaning. "Is there an integer `x` with `x > 3` and `x < 6`?"

```python
import z3
x = z3.Int('x')
s = z3.Solver()
s.add(x > 3, x < 6)
print(s.check(), s.model())      # sat [x = 4]
```

You describe constraints; Z3 either finds values satisfying them, or proves none exist.

---

## 2. The three answers

| Answer | Meaning | Is the claim settled? |
|---|---|---|
| `sat` | A solution exists. Z3 hands you a **model**. | Yes — you can check the model yourself |
| `unsat` | **No** solution exists. | Yes — proved (trusting Z3) |
| `unknown` | Z3 gave up (too hard, timeout, unsupported). | **No** |

In the repo these are `VerificationResult.FAILED / PROVED / UNKNOWN` (note the flip, explained next).

---

## 3. Why we assert `Not(goal)` and look for `unsat`

We want to know whether `assumptions ⇒ goal` is **valid** (true in every situation). Satisfiability asks the opposite sort of question ("is there *some* situation?"), so we use a trick:

```
   assumptions ⇒ goal   is valid
         ⇔
   assumptions ∧ ¬goal  is UNSATISFIABLE
```

If there were a situation making the assumptions true and the goal false, that would be a counter-example to the implication. So:

- `unsat` on `assumptions ∧ ¬goal` → implication valid → **PROVED**.
- `sat` → the model is a **counterexample** → **FAILED**.

```python
a, b = z3.Ints('a b')

# Valid:  a>0 and b>0  =>  a+b>0
s = z3.Solver(); s.add(a > 0, b > 0); s.add(z3.Not(a + b > 0))
print(s.check())                  # unsat        (so the claim is PROVED)

# Invalid:  a>0  =>  a>5
s = z3.Solver(); s.add(a > 0); s.add(z3.Not(a > 5))
print(s.check(), s.model())       # sat [a = 1]   (counterexample: a = 1)
```

This is literally the body of `verify_obligation`:

```python
for assumption in obligation.assumptions: solver.add(translate(assumption))
solver.add(z3.Not(translate(obligation.goal)))
result = solver.check()    # unsat -> PROVED, sat -> FAILED, else UNKNOWN
```

> **Common confusion — "`unsat` sounds like failure."**
> It's the *good* outcome here: unsat of the **negated** goal. Read it as "there is no way for the goal to be false."

> **Common confusion — "`sat` = the program works."**
> In this encoding `sat` means *a bug was found* (a case where assumptions hold and goal fails).

---

## 4. A model *is* a counterexample

The model is a table of values for the variables. The repo's `describe_failure` turns it into text for the LLM: "Counterexample (these values satisfy the assumptions but falsify the goal): x = -2 …". Its docstring records a real observation: a loop-body obligation was rejected with `x = -2`, which was precisely the evidence that the proposed invariant failed to exclude negative `x`.

That is why Z3 is good for LLM feedback: **a concrete failing case is a far better hint than "wrong".**

---

## 5. The square-root obligations, run for real

Using integers `N`, `x`; invariant `I: x*x ≤ N`, guard `G: (x+1)*(x+1) ≤ N`, postcondition `Q`, variant `V = N − x`:

```python
N, x = z3.Ints('N x')
I = x*x <= N
G = (x+1)*(x+1) <= N
Q = z3.And(x*x <= N, N < (x+1)*(x+1))

# Exit:  I and not G  =>  Q
s = z3.Solver(); s.add(I, z3.Not(G)); s.add(z3.Not(Q));  print("exit", s.check())     # exit unsat

# Body preserves the invariant (after x := x+1):  I and G  =>  (x+1)^2 <= N
s = z3.Solver(); s.add(I, G); s.add(z3.Not((x+1)*(x+1) <= N)); print("body", s.check())  # body unsat

# Variant strictly decreases and stays >= 0
V, V2 = N - x, N - (x+1)
s = z3.Solver(); s.add(I, G); s.add(z3.Not(z3.And(V2 < V, V2 >= 0))); print("variant", s.check())  # variant unsat
```

All three `unsat` → all three obligations proved. Note these *contain* `x*x` — nonlinear — yet Z3 solved them, because here the products appear **syntactically identically on both sides** and reduce, after normalisation, to linear reasoning over the atoms `x*x` / `x`. Don't over-generalise from that (next section).

---

## 6. Theories

A **theory** fixes the meaning of symbols. Z3 supports several; the ones that matter here:

### 6.1 Integers (LIA) and Reals (LRA) — the linear ones
Linear Integer Arithmetic: `+`, `-`, comparison, multiplication **by constants**. **Decidable and fast.**

```python
xi = z3.Int('xi'); s = z3.Solver(); s.add(xi > 0, xi < 1); print("int", s.check())   # int unsat
xr = z3.Real('xr'); s = z3.Solver(); s.add(xr > 0, xr < 1); print("real", s.check())  # real sat
```

Nothing is strictly between 0 and 1 for integers, plenty for reals. **The sort (Int vs Real) changes the answer** — which is why the repo's `ProofObligation` carries `params` ("give names their declared sort instead of defaulting every unbound name to Real"). Choosing the wrong sort can make a true thing false or vice-versa.

### 6.2 Nonlinear arithmetic (NIA/NRA)
Multiplying variables together: `x*y`, `x*x`.

- **Over the reals** it is *decidable* (Tarski; Z3 has a procedure, `nlsat`) but can be very slow:
  ```python
  r = z3.Real('r'); s = z3.Solver(); s.add(r*r == 2); print(s.check(), s.model())
  # sat [r = -1.4142135623?]       (an algebraic number; the '?' means "truncated display")
  ```
- **Over the integers** it is **undecidable** (Hilbert's 10th problem / Matiyasevich). No algorithm can always answer. Z3 uses heuristics and may return `unknown`:
  ```python
  y, z = z3.Ints('y z'); s = z3.Solver(); s.set("timeout", 2000)
  s.add(y*y*y + z*z*z == 3*y*z + 1000003, y > 1, z > 1)
  print("nl", s.check())           # nl unknown     (in my run; heuristic, may vary by version)
  ```

This is *the* source of `INCONCLUSIVE` attempts in the project (the history text in `agent/refiner.py` says exactly: "Z3 Verification was INCONCLUSIVE (timeout or non-linear arithmetic complexity)"). Square-root and anything with `x*x`, `N*N`, products of unknowns live in this danger zone.

### 6.3 Arrays
Z3's array theory has `Select(A, i)` (read) and `Store(A, i, v)` (write) with the obvious laws.

```python
A = z3.Array('A', z3.IntSort(), z3.IntSort()); i = z3.Int('i')
s = z3.Solver(); s.add(z3.Select(z3.Store(A, i, 5), i) != 5); print("arr", s.check())   # arr unsat
```
"Writing 5 at `i` then reading `i` always gives 5" — proved (the negation is unsat). Array specs in L_spec map to this.

### 6.4 Quantifiers (`∀`, `∃`)
Quantifiers make things hard. Z3 handles them by *instantiation heuristics* (pattern/E-matching, model-based): often works, no completeness guarantee.

```python
f = z3.Function('f', z3.IntSort(), z3.IntSort()); k = z3.Int('k')
s = z3.Solver(); s.add(z3.ForAll([k], f(k) > k)); s.add(f(0) <= 0); print("q", s.check())  # q unsat
```
Here it succeeded (instantiate `k := 0` to contradict `f(0) ≤ 0`). Harder combinations (quantifier alternation, nonlinear arithmetic inside quantifiers) commonly give `unknown` — or can run forever.

---

## 7. Why `unknown` happens, and timeouts

`unknown` has several causes:

1. **Undecidable fragment** (nonlinear integers, rich quantifiers).
2. **Incomplete heuristics** for a decidable-but-hard fragment.
3. **Resource limit:** a timeout or memory cap you set.
4. **Unsupported feature** in the encoding.

Z3 will tell you why:

```python
s = z3.Solver(); s.set("timeout", 1000)      # milliseconds
r = s.check()
if r == z3.unknown: print(s.reason_unknown())    # e.g. "timeout" or "incomplete (quantifiers)"
```
(I tried to force a timeout on a hard quantified formula, but Z3 decided that particular one instantly — a reminder that "looks hard" and "is hard for Z3" differ. The repo uses `solver.reason_unknown()` in its UNKNOWN message path.)

**Important operational point:** `z3_backend.py` now sets a solver timeout (10 s by default, override with the environment variable `FORMALLLM_Z3_TIMEOUT_MS`), so a pathological obligation ends as `UNKNOWN` instead of hanging; this was added on 2026-10-02 (see `10_Progress_Log.md`). Handling `UNKNOWN` more cleverly is partly done: an obligation that *times out* is now retried in up to four short runs, each built from scratch under its own random seed, before one patient run with the whole limit (2026-10-04; Z3's running time on a hard goal is wildly uneven, so a few restarts beat one long run; `14`, §5f), and a fallback to Lean or Coq exists for goals Z3 cannot decide (`--backend z3+lean`, `15`).

> **Common confusion — "`unknown` = the claim is false."**
> It's "undecided". Treat as not-proved, **but** don't blame the LLM's parameters for it: the model may have chosen a perfectly valid invariant that Z3 just can't handle. The repo's feedback text for INCONCLUSIVE already hints at this; a better system distinguishes the two.

---

## 8. Practical vocabulary

- **Assertion / constraint:** a formula added to the solver (`s.add`).
- **Satisfying assignment / model:** values that make all assertions true.
- **Sort:** type of a Z3 term (`IntSort`, `RealSort`, `BoolSort`, arrays…).
- **Validity vs satisfiability:** valid = true in all models; satisfiable = true in at least one. `valid(F) ⇔ unsat(¬F)`.
- **Tactic / strategy:** Z3 lets you script its internal procedures (`z3.Tactic('nlsat')`, `z3.Then(...)`). Choosing tactics is one way to rescue an `unknown`.
- **Quantifier-free:** no `∀/∃` — the sweet spot.

---

## 9. Where Z3 fits in the refinement loop

```
 LLM picks law + params
        │
        ▼
 law.apply(spec, params)  ──►  list of ProofObligations (assumptions ⇒ goal)
        │
        ▼ for each
 Z3Translator: L_spec AST ──► Z3 expression         (lspec/z3_translator.py)
        │
        ▼
 solver.add(assumptions); solver.add(Not(goal)); check()
        │
   ┌────┼──────────────┐
 unsat  sat           unknown
   │     │              │
 PROVED FAILED         UNKNOWN
 (go on) (counterexample → back to the LLM)   (INCONCLUSIVE → back to the LLM, weaker hint)
```

---

## 10. Check yourself

1. Why do we ask Z3 whether `assumptions ∧ ¬goal` is satisfiable?
2. You get `sat` and a model `x = -2`. What does that tell you about the refinement step?
3. Z3 returns `unknown` on a formula with `x*y*z`. List two possible reasons.
4. Why can `0 < v < 1` be satisfiable for `Real` and not for `Int`?
5. Why is an un-timed `check()` a robustness risk?
6. Run the §5 snippet yourself. Then change the invariant to `N < (x+1)*(x+1)` and re-check the "exit" and "body" obligations. What happens and why? (Hint: file 02, §6, "common confusion".)

<details><summary>Answers</summary>

1. Because `A ⇒ B` is valid exactly when there is no situation with `A` true and `B` false.
2. The step is invalid: with `x = -2` the assumptions hold but the goal fails — typically the invariant/intermediate is too weak and must be strengthened to exclude it.
3. Nonlinear integer arithmetic is undecidable/heuristic; a timeout or resource limit was hit.
4. There are real numbers (0.5) between 0 and 1 but no integers.
5. A pathological obligation can run for a very long time or forever, hanging the loop.
6. The "exit" obligation now fails: Z3 returns `sat` (I got `N = -8, x = -3`), because `N < (x+1)*(x+1)` alone no longer implies `x*x ≤ N`. The "body" obligation is still `unsat` (proved) — but only *vacuously*, because `N < (x+1)^2` and the guard `(x+1)^2 ≤ N` contradict each other, so the assumptions can never hold together. Moral: a step can be "proved" for a silly reason; an invariant also has to be true at the start (initialisation), which this one is not for large `N`.
</details>

---

*Next:* `09_Glossary.md` — a one-stop lookup for every term used in these notes.
