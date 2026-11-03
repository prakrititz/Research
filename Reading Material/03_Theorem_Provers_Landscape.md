# 03 — The Landscape of Provers and Checkers

> **Prerequisite:** `02_Formal_Methods_Primer.md`.
> **Goal:** know what the words *Z3, Vampire, Coq/Rocq, Lean, Isabelle, Dafny, CoqHammer* refer to, how they differ, and — crucially for this project — **which one makes the best partner for an LLM, and why.**

---

## 1. The big picture: a spectrum from "push button" to "you drive"

All of these tools answer the same kind of question: *"Is this logical statement true?"* They differ in **how much work you do** versus **how much they do**, and **how much you must trust them**.

```
   FULLY AUTOMATIC                                                   FULLY MANUAL
   (you ask, it answers)                                      (you write every step)
   ◄───────────────────────────────────────────────────────────────────────────────►

   SMT solvers      Automated (first-    Auto-active      Interactive proof assistants
   Z3, cvc5         order) provers       verifiers        Coq/Rocq, Lean 4, Isabelle
                    Vampire, E           Dafny, Why3

   weak logic,      FOL, powerful        programs +       very expressive logic,
   very fast        search               hints            YOU guide, tiny trusted core
```

The trade-off is almost universal: **the more expressive the logic (the more you can say), the less the tool can do by itself.**

---

## 2. Family 1 — SMT solvers (Z3, cvc5)

**SMT** = *Satisfiability Modulo Theories.* You give a formula mentioning integers, reals, arrays, bit-vectors etc. The solver answers one of three things:

- `sat` (here is a solution — "model"),
- `unsat` (no solution exists),
- `unknown` (gave up).

They are built for *quantifier-free* or lightly-quantified formulas over **built-in theories** of arithmetic and data structures. Within those theories they are astonishingly fast, which is why program verifiers and symbolic execution tools use them under the hood.

- **Z3** (Microsoft Research) — used by this project's current backend (`FormalLLM/verification/z3_backend.py`).
- **cvc5** (successor to CVC4) — a comparable solver.

**Strengths:** push-button; returns a **counterexample** when the claim is false; great at arithmetic.
**Weaknesses:** weak on nonlinear integer arithmetic (`x*x`!), on heavy quantifiers, and on induction (they basically cannot do "for all natural numbers n" proofs by induction without help). The answer is a *verdict*, not a human-checkable proof object (Z3 can emit proofs, but few users rely on them).
**Trust:** you trust a large, complex C++ program. Bugs in SMT solvers have been found and fixed over the years — rare, but the trusted base is big.

Deep dive: `06_Z3_and_SMT_Primer.md`.

---

## 3. Family 2 — Automated theorem provers for first-order logic (Vampire, E, …)

**First-order logic (FOL)** has `∀` and `∃` over individuals, functions and predicates, but no built-in notion of "the integers". Provers like **Vampire** and **E** search for a proof by *resolution/superposition*: they derive consequences of the axioms until they find a contradiction with the negated goal.

Use them when you have an axiomatised world (sets, groups, your own definitions) and want a proof found automatically. They're strong on pure logical reasoning with quantifiers, weaker on arithmetic than SMT solvers.

They also appear *inside* the next tools as "backends" — see **hammers** in Section 7.

---

## 4. Family 3 — Interactive proof assistants (Coq/Rocq, Lean 4, Isabelle)

These are different in kind. A **proof assistant** is a programming-language-like system in which:

- you write **definitions** (data types, functions, predicates),
- you state **theorems**,
- you build **proofs** step by step (usually with *tactics* — short commands that transform the goal),
- and a small piece of code called the **kernel** *re-checks* the finished proof from first principles.

```
   you / LLM / automation      kernel (tiny)
   ────────────────────────    ─────────────
   tactics, search, hints,  ─►  proof term  ─►  "type-checks?"  yes/no
   anything goes, can be                         ▲
   buggy and it's FINE                           └─ the ONLY thing you must trust
```

### 4.1 The de Bruijn criterion

A system satisfies the **de Bruijn criterion** if every proof is checked by a *small, independently auditable kernel*. All the clever, complicated automation lives *outside* the kernel and only has to produce something the kernel accepts. If the automation is buggy, at worst it fails to produce a proof — it can't make a false theorem pass.

This is the gold standard of trust: instead of trusting millions of lines of search code, you trust a few thousand lines.

### 4.2 Curry–Howard correspondence, in plain words

The deepest idea behind Coq and Lean (don't worry if it feels strange at first):

> **A proposition is a type. A proof of the proposition is a program (a value) of that type.**

| Logic | Programming |
|---|---|
| Proposition `A → B` ("A implies B") | Function type from `A` to `B` |
| Proof of `A → B` | A function that turns any proof of `A` into a proof of `B` |
| Proposition `A ∧ B` | Pair type `A × B` |
| Proposition `A ∨ B` | Sum (tagged union) type |
| Proposition `∀ n, P n` | Dependent function type (a function whose output *type* depends on the input) |
| `False` | A type with no values at all |

So "checking a proof" is **type-checking a program**. That's why the kernel can be small: type-checking is a well-understood, mechanical procedure. It also means these systems are simultaneously *programming languages* — you can define `sqrt` in Coq/Lean and prove it correct, in the same file.

### 4.3 The three systems

- **Coq → renamed Rocq.** French (INRIA), 1980s lineage. Logic: Calculus of Inductive Constructions (CIC). The project was renamed to *Rocq* around 2023–2025; older docs and the paper say Coq, and the `coqc` command still appears in many setups (see `04_Coq_Primer.md`). Famous for CompCert (verified C compiler).
- **Lean 4.** Newer (Leonardo de Moura, originally at Microsoft Research). Same family of type theory as Coq. Very active community around the **Mathlib** math library and growing use for verified software and AI-for-math. Fast, modern tooling. See `05_Lean_Primer.md`.
- **Isabelle/HOL.** Different logic (Higher-Order Logic, not dependent types). Strong automation via **Sledgehammer**; used heavily for verifying seL4 (an OS microkernel) and in many hardware/software projects.

**Strengths:** you can state *anything* mathematics can say; inductive proofs over unbounded data are natural; trust is minimal.
**Weaknesses:** steep learning curve; proofs are laborious; automation, while improving, is far weaker than a human expert.

---

## 5. Family 4 — Auto-active verifiers (Dafny, Why3, Boogie…)

These sit in the middle. You write a program **with annotations** (preconditions, postconditions, loop invariants — exactly the things from `02_...`) and the tool generates proof obligations and sends them to an SMT solver automatically. You never write tactics; you add *hints* (assertions, lemmas) when the solver gets stuck.

**Dafny** (Microsoft) is the best-known: it looks like a normal language, and green checkmarks appear in the editor when everything proves.

**Strengths:** practical for real code, good error messages.
**Weakness:** inherits SMT's limits; when it fails you debug *the solver's* confusion with hints.

Interesting connection to this project: the **refinement-calculus approach** (Refine4LLM) is a sibling of this idea — it, too, manufactures proof obligations and discharges them with an automated prover — but it derives the program *from* the spec instead of checking given code.

---

## 6. Comparison table

| | **SMT (Z3)** | **FOL provers (Vampire/E)** | **Coq / Rocq** | **Lean 4** | **Isabelle/HOL** | **Dafny** |
|---|---|---|---|---|---|---|
| Automation | Very high | High (logic only) | Low–medium (+hammer) | Low–medium (`omega`, `simp`, `aesop`…) | Medium–high (Sledgehammer) | High (via SMT) |
| Expressiveness | Limited theories | FOL | Very high (dependent types) | Very high | High (HOL) | Medium |
| Handles induction | Poor | Poor | Natural | Natural | Natural | Needs lemmas |
| Trusted base | Large solver | Large prover | **Small kernel** | **Small kernel** | **Small kernel** | Dafny + Boogie + Z3 |
| Output | sat/unsat/unknown + model | proof / "no proof found" | Machine-checked proof term | Machine-checked proof term | Machine-checked proof | Verified / error line |
| Counterexamples | **Yes (models)** | Sometimes | Not automatic | Some tools (`plausible`, `decide`) | `nitpick`, `quickcheck` | Often |
| Feedback to an LLM | Crisp: a concrete counterexample | Coarse | Rich *goal states*, but verbose | Rich goal states, structured | Rich | Line-based messages |
| Setup effort | `pip install z3-solver` | Install binary | Heavy-ish | Moderate (`elan`) | Heavy-ish | Moderate |

> **Common confusion — "Coq/Lean are just stronger Z3."**
> They're a different *kind* of thing. Z3 *decides* statements in fixed theories; Coq/Lean let you *define new theories* and *construct proofs*, with a tiny kernel guaranteeing them. Z3 says "unsat" and you trust Z3. Coq says "Qed" and you trust a small kernel.

> **Common confusion — "proved in Z3 = proved in Coq."**
> The *claim* may be identical, but the *evidence* differs. A Coq proof can be re-checked by anyone with the kernel; a Z3 "unsat" is a verdict from a bigger program.

---

## 7. Hammers (including CoqHammer)

Proof assistants are laborious because humans must guide every step. A **hammer** is a bridge that tries to automate the boring ones:

```
   goal in Coq/Isabelle/Lean
        │ 1. select relevant facts from the library (hard part!)
        │ 2. translate goal + facts to FOL/SMT
        ▼
   external automated prover (Vampire, E, cvc, Z3 ...)
        │ 3. prover finds a proof (or returns which facts it used)
        ▼
        │ 4. RECONSTRUCT a proof inside the proof assistant
        ▼
   kernel re-checks  ✔   (so the external prover need not be trusted!)
```

Step 4 is the clever bit: the external prover is only used as a *search heuristic*; the final proof is rebuilt in the kernel's own language, so the de Bruijn criterion survives.

- **Sledgehammer** — the Isabelle hammer (the original).
- **CoqHammer** — the Coq hammer, by Czajka and Kaliszyk ("Hammer for Coq: Automation for dependent type theory", 2018). The Refine4LLM paper (see `04_Coq_Primer.md` §9) says it uses CoqHammer and, through it, four automated provers: **cvc4, Vampire, E, and Z3**. In Coq the user-facing tactics are named `hammer` and `sauto`/`qauto`.
- For Lean, tools in the same spirit exist (e.g. `aesop` for proof search, `omega` for linear arithmetic over ℕ/ℤ, `simp` for rewriting); this primer does not claim a Lean "CoqHammer-equivalent" is as mature — I haven't verified that, so check the current Lean tooling before relying on it.

---

## 8. Which one is the best partner for an LLM?

Think of three things an LLM-in-a-loop needs from its checker:

1. **Soundness** — so hallucinations can't sneak through.
2. **Actionable feedback** — so the next attempt can be better.
3. **Speed / reliability** — hundreds of calls per benchmark.

| Checker | Soundness | Feedback | Speed |
|---|---|---|---|
| Z3 | trusted-but-large | **excellent for false claims** (concrete counterexample); poor for `unknown` | very fast |
| Coq / Lean | **best** (small kernel) | rich but *textual*: the unsolved goal + error messages | slower (process start, library load) |

This project's honest current position: Z3 is a good first choice because **refinement obligations are mostly arithmetic implications** where a counterexample teaches the LLM exactly what went wrong (the repo's own `describe_failure` docstring documents a measured example). The weak spot is nonlinear integer arithmetic and `unknown` — which is where a proof assistant (with induction and `nia`/`lia`/`omega`-style tactics) could add robustness. That trade-off is the subject of the project-direction notes in this folder.

---

## 9. Check yourself

1. What does `unknown` from Z3 mean, and how is it different from `unsat`?
2. State the de Bruijn criterion in one sentence. Why does it make a hammer's external prover "untrusted but harmless"?
3. In Curry–Howard terms, what is a proof of `A → B`?
4. Why can an SMT solver not easily prove "for all `n`, `0 + 1 + … + n = n(n+1)/2`", while Coq/Lean can?
5. Name one advantage and one disadvantage of using Coq/Lean (instead of Z3) as the checker in an LLM loop.
6. What are the four automated provers CoqHammer drives in the paper's setup?

<details><summary>Answers</summary>

1. "I couldn't decide" — nothing is proved or refuted. `unsat` (for the negated goal) means proved.
2. Every proof is re-checked by a small auditable kernel. The hammer rebuilds the proof in the kernel, so a buggy external prover can only fail, not cause a false theorem to pass.
3. A function that turns any proof of `A` into a proof of `B`.
4. It needs induction over unbounded `n`, which is native in proof assistants (the `induction` tactic) but not in SMT's decision procedures.
5. Advantage: tiny trusted kernel and induction support. Disadvantage: heavier setup/slower, less crisp feedback than a counterexample, laborious proofs.
6. cvc4, Vampire, E and Z3.
</details>

---

*Next:* `04_Coq_Primer.md` and `05_Lean_Primer.md` (read both or just the one you're curious about), then `06_Z3_and_SMT_Primer.md`.
