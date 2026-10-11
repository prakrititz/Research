# 09 — Glossary

Alphabetical. Terms are used across files 02–06. "(repo)" marks where a term shows up in this project's code.

**Assertion** — A logical formula handed to a solver (`solver.add(...)`) or placed in code as a claim that must hold at that point.

**Assignment (law)** — Refinement law that replaces a spec by `x := E` when substituting `E` for `x` in the postcondition is implied by the precondition. A terminal law: yields code. (repo: `refinement/laws/assignment.py`)

**Assumption** — A fact taken as true while proving something; the left side of `assumptions ⇒ goal`. (repo: `ProofObligation.assumptions`)

**ATP (Automated Theorem Prover)** — A program that searches for proofs by itself, e.g. Vampire, E, Z3, cvc5.

**Auto-active verifier** — A tool (Dafny, Why3) where you annotate programs and an SMT solver proves the obligations automatically; you only add hints.

**Axiom** — A statement accepted without proof as a starting point of a logic or theory.

**Bound variable** — A variable introduced by a quantifier (`∀x. …`); it is a placeholder, not a particular value. Contrast with *free variable*.

**Gödel incompleteness** — (Background) A result showing that any sufficiently rich logic has true statements it cannot prove, and no algorithm decides all arithmetic truths. Explains why `unknown` is unavoidable.

**Cvc5 / CVC4** — A family of SMT solvers, alternatives to Z3. CVC4 was one of the provers used by CoqHammer in the Refine4LLM paper.

**Coq / Rocq** — A proof assistant and functional language based on the Calculus of Inductive Constructions; renamed Rocq. Used by the Refine4LLM paper. (file 04)

**CoqHammer** — A Coq plugin (tactics `hammer`, `sauto`, `qauto`) that sends goals to external provers and reconstructs the proof inside Coq.

**Counterexample** — A concrete assignment of values making the assumptions true and the goal false, proving an implication invalid. Z3 returns it as a *model*. (repo: `describe_failure`)

**Curry–Howard correspondence** — The identification of propositions with types and proofs with programs; the reason type-checking can verify proofs.

**de Bruijn criterion** — Design principle: all proofs are re-checked by a small, auditable kernel, so automation can be arbitrarily complicated without being trusted.

**Decidable** — A problem for which an algorithm always halts with the right yes/no answer. Linear integer arithmetic: decidable. Nonlinear integer arithmetic: not.

**Dependent type** — A type that depends on a value, e.g. "vectors of length `n`". Lets types express rich propositions.

**Discharge (an obligation)** — To prove a proof obligation, thereby permitting the refinement step to proceed.

**Entailment (`⇒`, ⊨)** — `A ⇒ B`: whenever `A` is true, `B` is true.

**Existential quantifier (`∃`)** — "There exists a value such that…".

**Frame (of a spec)** — In `x:[P,Q]`, the list of variables (`x`) the program may modify; everything else must stay unchanged. (repo: `refinement/frame.py`, issue #1)

**Free variable** — A variable not bound by any quantifier; its value comes from the program state.

**First-order logic (FOL)** — Logic with `∀`, `∃`, `∧`, `∨`, `¬`, `⇒` over individuals, functions, and predicates (but not over predicates themselves).

**Gallina** — The functional language/term language of Coq.

**Goal (proof assistant)** — The statement still to be proved at the current step, shown below the `====` line with hypotheses above.

**Guard** — The loop condition `G` in `while G do …`. (repo: `iteration.py` parameter `guard`)

**Hallucination (LLM)** — Fluent but false output produced by a language model; the failure the checker is there to catch.

**Hammer** — A tool that bridges a proof assistant and external ATPs: select facts, call prover, reconstruct the proof.

**Hoare triple** — `{P} C {Q}`: if `P` holds before `C` and `C` terminates, `Q` holds after.

**Hypothesis** — An assumption available in the current context of a proof (`H : x < y`).

**Induction** — Proof technique for inductive data: prove the base case and prove that holding for a smaller case implies holding for the next.

**Inductive type** — A type defined by listing its constructors (`O`/`S` for numbers, `nil`/`cons` for lists).

**Interactive theorem prover** — See *proof assistant*.

**Invariant (loop)** — A condition true before the loop, preserved by each iteration, hence true at exit; combined with `¬G` it must imply the postcondition. (repo: IterationLaw)

**Isabelle/HOL** — A proof assistant based on higher-order logic, known for Sledgehammer and the seL4 verification.

**Kernel (proof assistant)** — The small core that type-checks proof terms; the only part that must be trusted.

**Lake** — Lean 4's build system and package manager.

**Law (refinement)** — A rule that replaces a specification by code or by smaller specifications while preserving correctness, subject to proof obligations. (repo: `refinement/laws/`)

**Lean 4** — A modern proof assistant and programming language; home of Mathlib. (file 05)

**Lean REPL / LeanDojo** — Tools for driving Lean programmatically / for ML research on Lean proofs.

**`lia` / `omega`** — Coq's and Lean's built-in decision procedures for linear integer arithmetic.

**Linear arithmetic** — Arithmetic where variables are only added, subtracted, or multiplied by constants (no `x*y`).

**L_spec** — The project's specification language: first-order logic plus program-state notation, designed as a subset of Coq's language. (repo: `FormalLLM/lspec/`)

**LPL** — The project's small imperative target language (assignments, skip, sequence, if, while). (repo: `FormalLLM/lpl/`)

**Mathlib** — Large community library of formalised mathematics for Lean 4.

**Model (SMT)** — An assignment of values satisfying a formula; for a negated goal it is a counterexample.

**Strengthen / weaken** — Making a condition more demanding (strengthen: fewer states satisfy it) or less demanding (weaken: more states satisfy it). Used by the `strengthen_post` and `weaken_pre` laws.

**Neuro-symbolic** — Combining neural networks (LLMs) with symbolic reasoning (logic, provers).

**Nonlinear arithmetic** — Arithmetic including products of variables (`x*x`); hard for solvers, undecidable over integers.

**Obligation (proof)** — A logical statement that must be proved before a refinement step is accepted. (repo: `ProofObligation`)

**Partial correctness** — If the program terminates, the postcondition holds. Does not forbid infinite loops.

**Postcondition (Q)** — What is guaranteed true after the program runs.

**Precondition (P)** — What must be true before the program runs (the caller's obligation).

**Proof assistant** — A system where a human (or LLM) builds machine-checked proofs interactively, e.g. Coq/Rocq, Lean, Isabelle.

**Proof term** — The explicit object (a program, by Curry–Howard) that a kernel checks as the proof of a theorem.

**Quantifier** — `∀` ("for all") or `∃` ("there exists").

**`Qed`** — Coq command ending a proof and sending it to the kernel.

**Refinement (`⊑`)** — `S ⊑ T`: `T` is a correct implementation (or more detailed version) of `S`.

**Refinement calculus** — A mathematical framework of laws for deriving correct programs from specifications step by step. The theory behind this project.

**Refine4LLM** — The paper "Automated Program Refinement: Guide and Verify Code LLM with Refinement Calculus", which this repo re-implements.

**Rewrite (tactic)** — Replace occurrences of one expression with an equal one using an equation.

**SAT** — Boolean satisfiability: is there a true/false assignment making a formula true?

**Satisfiable** — A formula for which at least one model exists.

**seL4** — A formally verified operating-system microkernel (Isabelle/HOL), a landmark of formal verification.

**SMT** — Satisfiability Modulo Theories; SAT extended with integers, reals, arrays, etc.

**Sledgehammer** — Isabelle's hammer.

**Soundness** — A checker never accepts a false statement.

**Specification** — A precise statement of what a program must do, usually a pre/postcondition pair.

**Substitution** — Replacing a variable by an expression in a formula (`Q[E/x]`); the basis of the assignment rule. (repo: `lspec/substitution.py`)

**Tactic** — A command in a proof assistant that transforms the current goal (`intros`, `simp`, `lia`).

**Termination** — The program eventually halts; shown with a variant.

**Theory (SMT)** — A fixed meaning for a family of symbols (integer arithmetic, arrays, bit-vectors).

**Total correctness** — Terminates **and** satisfies the postcondition.

**Trusted computing base (TCB)** — The code you must trust for a guarantee to hold (for Coq/Lean, the kernel; for Z3, the solver).

**`unknown`** — Z3's third answer: undecided. Not a proof and not a refutation. (repo: `VerificationResult.UNKNOWN`, `AttemptStatus.INCONCLUSIVE`)

**`unsat` / `sat`** — Unsatisfiable / satisfiable. For a negated goal, `unsat` means the goal is valid.

**Valid** — True in every model. `F` is valid iff `¬F` is unsatisfiable.

**Variant (loop)** — A non-negative quantity that strictly decreases each iteration, proving termination. (repo: `iteration.py` parameter `variant`)

**Verification condition (VC)** — Another name for a proof obligation, usually one generated from a program by weakest precondition.

**Weakest precondition (wp)** — The most general condition guaranteeing a postcondition after a program; `{P}C{Q}` holds iff `P ⇒ wp(C,Q)`.

**Well-founded** — An ordering with no infinite descending chain (like `<` on the naturals); the reason a decreasing variant forces termination.

**Z3** — Microsoft Research's SMT solver; this project's verifier. (file 06)
