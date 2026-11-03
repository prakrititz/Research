# 02 — Formal Methods Primer: What Does "Correct Program" Even Mean?

> **Who this is for:** you, today. No prior knowledge assumed.
> **Goal:** by the end you can read the project's central example (integer square root) and explain, in your own words, *why* it is correct and *what a machine must check* to be sure.
> **Reading time:** ~45 minutes. Do the "check yourself" quiz at the end.

---

## 0. The one-paragraph version

A program is **correct** only relative to a **specification** — a precise statement of what it is supposed to do. *Formal methods* means: write the specification in math, and then use math (proofs, checked by a machine) to show the program meets it. Testing shows the program works on the inputs you tried. A proof shows it works on **all** inputs that satisfy the specification. This project (FormalLLM) uses a Large Language Model (LLM) to *propose* the proof steps and a mechanical checker (Z3) to *accept or reject* them, so the LLM's mistakes can never leak into the final answer.

---

## 1. "It works" is not a sentence

Suppose I say "this function computes the square root." Questions immediately arise:

- Square root of what? Negative numbers? Non-integers?
- What does it return for 10? 3? 3.16? "Roughly 3"?
- What if the input is huge?

"Correct" has no meaning until those are answered. The answers *are* the specification.

```
         informal idea            specification              program
   "compute the sqrt"   ───►   precise math statement   ───►   code
        (fuzzy)                   (unambiguous)              (executable)
                                       ▲                         │
                                       └──── is the code ────────┘
                                             faithful to it?   ← formal methods
                                                                 answers THIS question
```

> **Common confusion — "the proof shows my program is right."**
> No. The proof shows the program matches the **spec**. If the spec is wrong (you wrote the wrong math), you've proven the wrong thing. Formal methods moves the risk from "is my code right?" to "is my spec right?" — a much smaller, more readable thing to audit. This is a real limitation, and it is why this project cares about *how specs are written*, not only about code.

---

## 2. Specifications: precondition and postcondition

The simplest, most useful way to specify a program is a pair of logical statements about **program state** (the values of variables):

- **Precondition `P`** — what must be true *before* the program runs. It's the caller's promise.
- **Postcondition `Q`** — what will be true *after*. It's the program's promise.

It's a contract: *if you give me inputs satisfying P, I guarantee outputs satisfying Q.* If P is violated, the contract says nothing — the program may do anything (crash, loop, return garbage). That is not a bug in the contract; it's the definition.

### Running example: integer square root

We have a natural number `N ≥ 0`. We want the integer `x` such that `x` is the biggest whole number with `x·x ≤ N`. For N = 10 that is 3 (since 3·3 = 9 ≤ 10 but 4·4 = 16 > 10).

```
   P  :   N ≥ 0
   Q  :   x*x ≤ N   ∧   N < (x+1)*(x+1)
```

Read `Q` out loud: "x squared doesn't exceed N, but the next integer's square does." That pins x down uniquely. Notice: `Q` says *what* x is, not *how* to compute it. That separation — **what vs. how** — is the heart of everything.

(In this repo you will see this written with `/\` for "and": `x*x <= N /\ N < (x+1)*(x+1)`. Same thing. The project's tests, e.g. `FormalLLM/tests/test_fallback.py`, use exactly this example.)

### The `x:[P, Q]` notation (the "specification statement")

Refinement calculus (the theory this project is built on, explained fully in `08a_Refinement_Calculus_Explained.md`) writes a spec as a *program-shaped thing*:

```
   x : [ P , Q ]
   │     │   └── postcondition
   │     └────── precondition
   └──────────── the "frame": the variables this program is ALLOWED to change
```

Read: "a program that may change only `x`, which, started in a state satisfying `P`, ends in a state satisfying `Q`." It's a **placeholder for code that doesn't exist yet**. The whole game is to replace that placeholder with real code in small, safe steps.

---

## 3. Hoare triples: stating that a program meets a spec

Tony Hoare (1969) introduced a notation that relates a program `C` to a pair of conditions:

```
        { P }  C  { Q }
```

Meaning (**partial correctness**): *If `C` starts in a state satisfying `P`, and `C` finishes, then the final state satisfies `Q`.*

Note the "and C finishes". Two flavours:

| Flavour | Promise | Loops forever allowed? |
|---|---|---|
| **Partial correctness** | If it terminates, the answer is right | Yes (vacuously OK) |
| **Total correctness** | It terminates **and** the answer is right | No |

This project aims at **total correctness**, which is why loops need a *variant* (Section 6).

### Tiny examples

```
{ x = 5 }        y := x + 1        { y = 6 }          ✔ true
{ x ≥ 0 }        y := x + 1        { y > 0 }          ✔ true
{ true }         y := x + 1        { y = 6 }          ✘ false (x could be 100)
```

### The assignment rule (the only "axiom" you need right now)

To prove `{ ? } x := E { Q }`, take `Q` and **replace every `x` in it by `E`**. The result is the weakest thing you could require beforehand.

```
   Q  :   y > 0
   program:   y := x + 1
   replace y by (x+1) in Q:    x + 1 > 0
   so   { x + 1 > 0 }   y := x + 1   { y > 0 }
```

That "replace `x` by `E`" operation is called **substitution**, and the project has a file for it: `FormalLLM/lspec/substitution.py`. When you see the `assignment` law in the code, this is what it relies on.

---

## 4. Weakest precondition (wp)

Given a program `C` and a goal `Q`, the **weakest precondition** `wp(C, Q)` is the *most general* condition that guarantees `Q` after running `C`. "Weakest" means "allows the most starting states".

```
   wp(x := E, Q)   =   Q[E/x]            ("Q with E substituted for x")
   wp(C1 ; C2, Q)  =   wp(C1, wp(C2, Q))  (work backwards through the sequence)
```

Intuition: it is like asking, "to land at this destination, where must I start?" and walking the route in reverse.

Why you should care: **`{P} C {Q}` is true exactly when `P ⇒ wp(C, Q)`.** So proving a program correct reduces to proving *one logical implication*. Notice what that did: we turned a statement about *running code* into a statement about *pure logic*. A machine can check pure logic. That implication is called a **proof obligation** (or "verification condition").

> **Terminology you'll see everywhere in this project:** *proof obligation* = a logical statement that must be shown true before a refinement step is allowed. In the repo: `FormalLLM/verification/proof_obligations.py`.

---

## 5. Entailment ("⇒"): what the machine actually checks

`A ⇒ B` ("A entails B") means: in every situation where A is true, B is also true.

A machine can't enumerate every situation (there are infinitely many integers), so it uses a trick that you'll see over and over in `06_Z3_and_SMT_Primer.md`:

```
     A ⇒ B   is valid
        ⇔
     "A ∧ ¬B" has NO solution          (there is no situation where A holds but B fails)
```

Ask the solver to *find* a situation where `A` is true and `B` is false:
- It says **"none exists"** (unsat) → the implication is valid → ✔ obligation discharged.
- It says **"here's one"** (sat) → the implication is false, and the situation it found is a **counterexample**, which is gold: it tells you *why* you were wrong.

This is exactly what `verify_obligation` does in `FormalLLM/verification/z3_backend.py`: it adds the assumptions, adds `Not(goal)`, and calls `solver.check()`.

---

## 6. Loops: invariants and variants

Straight-line code is easy (substitute backwards). **Loops are where programs get hard to verify**, because a loop can run any number of times — you can't unroll infinitely.

### 6.1 The loop invariant

A **loop invariant** `I` is a statement that:
1. is true **before** the loop starts (initialisation),
2. if true at the **start** of an iteration, is still true at the **end** of that iteration (preservation),
3. therefore is true when the loop exits — *no matter how many iterations ran.*

It's **induction** for programs: base case (1) + inductive step (2) ⇒ always true.

```
   while G do body            G = "guard": loop continues while G true

                  ┌──────────────────────────────┐
   init  ───────► │  I holds                     │
                  │     │                        │
                  │     ▼  if G                  │
                  │   body ───► I still holds ───┘ (loop around)
                  │     │
                  │     ▼  if ¬G  (exit)
                  └──►  I ∧ ¬G   holds  ──►  must be enough to imply Q
```

The exit condition is the key obligation: **`I ∧ ¬G ⇒ Q`**. The invariant, plus "the loop has stopped", must give you the postcondition.

### 6.2 The variant (termination)

An invariant alone proves *partial* correctness. To rule out infinite loops, supply a **variant** `V`: an expression that
- is always `≥ 0` (a natural number — can't decrease forever), and
- **strictly decreases** every iteration.

Since you can't decrease a natural number forever, the loop must stop. (This is called a "well-founded" measure.)

### 6.3 Full worked example: integer square root

Goal: `x : [ N ≥ 0 , x*x ≤ N ∧ N < (x+1)*(x+1) ]`.

Naive algorithm: start `x = 0`, keep incrementing while `(x+1)*(x+1) ≤ N`.

```
   x := 0 ;
   while (x+1)*(x+1) <= N do
       x := x + 1
```

Choose:

| Piece | Choice | Why |
|---|---|---|
| Invariant `I` | `x*x ≤ N` | "x hasn't overshot yet" |
| Guard `G` | `(x+1)*(x+1) ≤ N` | "x+1 still doesn't overshoot" |
| Variant `V` | `N − x` | shrinks by 1 each step; never negative while `x*x ≤ N` |

The three obligations (each is a pure-logic statement a machine can check):

1. **Initialisation:** after `x := 0` and given `N ≥ 0`: `0*0 ≤ N`. ✔ trivial.
2. **Exit:** `I ∧ ¬G ⇒ Q`:
   `x*x ≤ N ∧ ¬((x+1)*(x+1) ≤ N)  ⇒  x*x ≤ N ∧ N < (x+1)*(x+1)`.
   `¬(A ≤ B)` is `B < A`, so the right side is literally what the left side says. ✔
3. **Body preserves invariant and decreases variant:** assume `I ∧ G` (i.e. `x*x ≤ N` and `(x+1)*(x+1) ≤ N`); after `x := x+1`, the new `x` is the old `x+1`, so the new invariant `x'*x' ≤ N` becomes `(x+1)*(x+1) ≤ N` — which is exactly `G`. ✔ And `V' = N − (x+1) < N − x = V`, with `V' ≥ 0` because `(x+1)*(x+1) ≤ N` with `x ≥ 0` forces `x+1 ≤ N`... (for the machine this is another one-line check).

I ran the exit, body and variant obligations through Z3 while writing this primer; all three came back `unsat` for the negated goal, i.e. **valid**. (Snippets in `06_Z3_and_SMT_Primer.md`.)

> **Common confusion — "the invariant is the postcondition."**
> No. The invariant is *weaker than where you're going*: it's true all the way through. Only at exit, combined with `¬G`, does it become `Q`. In the square-root example, `x*x ≤ N` holds at every step but `N < (x+1)*(x+1)` only holds at the end — that second half is `¬G`.

> **Common confusion — "finding the invariant is mechanical."**
> It's the creative step, and in general it cannot be fully automated. *This is precisely where the project asks the LLM for help* — the LLM proposes `I`, `G`, `V`; the solver checks them. If the LLM picks a bad invariant, the solver produces a counterexample and the LLM tries again. (See `FormalLLM/refinement/laws/iteration.py` and `describe_failure` in `z3_backend.py`.)

---

## 7. Refinement: derive the program from the spec

Instead of *writing code then proving it*, **refinement** goes the other way: start from the spec and transform it by small **laws**, each one *provably* preserving correctness, until only executable code remains.

```
      x:[P, Q]                        ← spec (a placeholder)
        │  apply law "sequential"
        ▼
   x:[P, R] ; x:[R, Q]                ← two smaller specs
        │  apply law "iteration"   (on the second)
        ▼
   x:[P, R] ; while G do x:[R∧G, R∧V<V0]
        │  apply law "assignment"  (on each leaf)
        ▼
   x := 0 ; while G do (x := x+1)     ← real code. Correct by construction.
```

Each arrow is only allowed if its **proof obligations** hold. "Correct by construction" = there's never a moment where you have unverified code; every intermediate state is correct-by-the-previous-step.

The symbol `⊑` ("is refined by") expresses it: `spec ⊑ program` means the program is a legitimate implementation of the spec. Look at the docstring in `iteration.py`: `x:[P,Q] ⊑ x:[P,I] ; while G do x:[I ∧ G, I ∧ V < V0]`. That *is* the iteration law, straight from the paper. `V0` is "the value V had at the start of this iteration", needed so we can say "V got smaller".

---

## 8. Proofs vs. testing

| | Testing | Formal proof |
|---|---|---|
| Covers | The inputs you tried | **Every** input satisfying `P` |
| Can show bugs | Yes | Yes (counterexample) |
| Can show absence of bugs | **No** (Dijkstra's famous remark) | Yes, relative to the spec |
| Cost | Cheap | Expensive (expertise, time) |
| Weak point | Missed cases | Wrong spec; bugs in the prover/checker; model of the machine differs from reality |

Example of testing's blind spot: a `sqrt` that is right for every N below 2 million and wrong at 2,000,001 because of an overflow. Random tests pass; a proof about mathematical integers... also passes, **because the proof was about ideal integers, not 32-bit ones.** Proofs are only as faithful as the model. Both tools are needed.

---

## 9. Soundness, completeness, decidability (the three words everyone throws around)

- **Sound:** the checker never accepts something false. *("If it says proved, it's proved.")* This is the property you demand from a verifier. A sound checker can still say "I don't know."
- **Complete:** the checker accepts everything true. In rich logics this is **impossible** to achieve with a terminating algorithm (Gödel, Turing, Church).
- **Decidable:** there is an algorithm that always terminates with a correct yes/no. Linear arithmetic over integers? Decidable. Integers with arbitrary multiplication and `∀`? **Undecidable.** Real-number polynomial arithmetic? Decidable but very slow in the worst case.

The practical upshot, which governs this project's design:

```
   Solver answers:   PROVED   ←  sound: trust it
                     FAILED   ←  counterexample: trust it (you can check it)
                     UNKNOWN  ←  "I gave up". NOT the same as false!
```

`UNKNOWN` happens a lot with nonlinear integer arithmetic (like `x*x`). In the repo it becomes `AttemptStatus.INCONCLUSIVE`. The system must treat it as *not proved* (conservative), never as success.

> **Common confusion — "UNKNOWN means the program is wrong."**
> It means *the tool couldn't decide*. The statement may be perfectly true.

---

## 10. Why this meets LLMs: the neuro-symbolic idea

**What LLMs are good at:** guessing plausible, creative, human-like text — including plausible invariants, plausible code, plausible law choices.
**What LLMs are bad at:** guaranteeing anything. They produce *fluent* output with no internal "proof-checker". They hallucinate: confidently state something false. Code that "looks right" and passes a few tests but violates the spec is the classic failure.

**What a solver/prover is good at:** certainty. It's slow at *inventing* but fast and exact at *checking*.

Combine them:

```
          ┌───────────────┐   proposal (law + parameters)    ┌──────────────┐
          │      LLM      │ ───────────────────────────────► │   Checker    │
          │ (creative,    │                                  │ (Z3: sound,  │
          │  fallible)    │ ◄─────────────────────────────── │  rigid)      │
          └───────────────┘   ACCEPT, or counterexample       └──────────────┘
                 ▲                      │
                 └──── try again ───────┘
```

The key asymmetry (this is a principle, not a detail): **checking is easier than finding.** Verifying a proposed invariant is a mechanical question; inventing it is a hard one. So you let the weak-but-creative part guess, and the strong-but-rigid part vet. A wrong guess costs a retry, not a wrong answer. The output program is trustworthy *regardless of how bad the LLM is*; a worse LLM just needs more retries (this is what the repo's benchmark logs measure across different models).

This is called **neuro-symbolic AI**: neural (the LLM) + symbolic (logic/proof).

> **Trust boundary:** you now trust the *checker*, not the LLM. So the quality of the whole system is bounded by the checker's soundness and by whether the *spec* is right. That is why people care about checkers with tiny trusted cores — see `03_Theorem_Provers_Landscape.md` (the "de Bruijn criterion"), and why this folder also discusses Coq and Lean, whose kernels are small.

---

## 11. Check yourself

1. In `{ P } C { Q }`, who "promises" what? What happens if `P` is false at the start?
2. Compute `wp(y := x*2, y > 10)`. (Answer: `x*2 > 10`, i.e. `x > 5`.)
3. For the square-root loop, why is `x*x ≤ N` a good invariant but `N < (x+1)*(x+1)` a bad one? (Hint: is the bad one true at the start, when `x = 0` and `N` is large?)
4. Why does the proof need a *variant*? What can go wrong with only an invariant?
5. A solver returns `UNKNOWN` on an obligation. Should the refinement step be accepted? Why not?
6. In one sentence: why is it *safe* to let an LLM propose proof steps?

<details><summary>Answers (try first!)</summary>

1. Caller promises `P`; program promises `Q`. If `P` is false the contract says nothing — anything may happen.
2. `x*2 > 10`.
3. `N < (x+1)*(x+1)` is false at the start for big N (x=0 → N < 1), so it isn't established by initialisation; it only becomes true at exit.
4. Without a variant the loop might never stop; you'd only have partial correctness.
5. No: UNKNOWN is "not proved". Accepting it would let unverified steps in and break soundness.
6. Because every proposal is independently checked by a sound checker, so a wrong guess is rejected rather than trusted.
</details>

---

*Next:* `03_Theorem_Provers_Landscape.md` — the tools that do the checking, and how they differ.
