# 18 — Questions for Dr. Hou (a page you can forward)

> Written so it can be sent as it is. Each question says what we found, why it matters for reproducing the paper, and what we will do either way. Numbers marked **(see 14)** are in `14_Reliability_Study.md`.

---

**Subject: Reimplementation of Refine4LLM — four questions that block an exact reproduction**

Dear Professor Hou,

We have reimplemented the refinement loop of *Automated Program Refinement* in Python (Z3 for the search, Coq and Lean 4 to certify finished derivations). On your motivating example, the square root within an error bound, a general (not square-root-specific) prompt now lets `gpt-oss:120b` derive a verified program in 2–5 model calls **(see 14 for the success counts over repeated trials)**. Four points stop us from reproducing the paper's numbers exactly; we would be grateful for your guidance on them.

**1. The invariant in Fig. 2 and the variant decrease.**
Fig. 2 uses the invariant `x² ≤ N`, the guard `(x+e)² ≤ N`, the variant `N − (x+e)²` (or `N − x²`) and the body `x := x + e`. Our prover accepts the loop body only if the invariant also says `x ≥ 0`: with `x = −3, e = 1, N = 10` the invariant and guard hold, but `N − (x+e)²` *increases* after `x := x + e`. So either (a) the figure abbreviates an invariant that also contains `x ≥ 0` (and a precondition that makes `x ≥ 0` available), or (b) the check in Coq is only invariant preservation (partial correctness) and termination is argued elsewhere, or (c) Lemma 6.7's variant condition is weaker than the one we implemented. Which is it? *(We currently support all three levels: total, decreasing-only, partial; we report which one a derivation reached.)*

**2. The formal specifications for HumanEval and the library of learned laws.**
Section 9.1 says the specifications were "adapted from the BigCode project and manually checked". Could you share them, together with the 164 prompts and the library used for Table 8? Without them an exact reproduction of Table 6 is impossible: we wrote our own specifications for a 12-problem pilot (each checked against the reference solutions on every HumanEval and EvalPlus test input, and shown to reject perturbed outputs), but they are ours, not yours, and they cover only problems whose result is a number or a truth value (53 of 164 by signature).

**3. The specification and program languages.**
Our `L_spec` has `+ − × ÷`, comparisons, quantifiers and read-only arrays; our `L_pl` has scalar assignment, sequence, `if`, `while`. For the 111 HumanEval problems with list results, strings, dictionaries or tuples, how does your `L_spec`/`L_pl` express them — array element assignment, strings as arrays of characters, built-in functions such as `sum`, `len`, `%`, `sorted` (or Coq functions)? The paper says `L_spec` is "a subset of the language of Coq"; are Coq's standard functions available inside specifications?

**4. How Table 6 was run.**
For each of the 164 problems: one derivation or the best of several? What temperature and call budget? Does "fall back after more than 5 failures" (Algorithm 1) count failures per specification or per run? And is the Table 6 pass criterion exactly the original tests plus EvalPlus' tests, with the program emitted from the Coq derivation by the extraction described in Section 8?

Two smaller things we found that may interest you:
* Making a loop invariant *too strong* (for example, restating the guard inside it) makes the loop body unsatisfiable at the boundary; checking "every sub-specification created by a step is feasible" (`pre ⇒ ∃ x′. post`) rejects such a step immediately and removed a whole class of long failures.
* With Coq's standard tactics, quantified obligations on arrays (Linear Search, Max Element) were certified in 9 of 21 cases; Lean 4's `grind` certified 21 of 21. We expect CoqHammer with external provers to close the gap, as in your pipeline, but have not installed those provers.

With thanks for the paper and for any help with these points,
[your name]
