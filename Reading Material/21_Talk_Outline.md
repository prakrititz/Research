# 21 — A 10-minute talk outline for the meeting with Dr. Hou

> Eight slides. Each has what to say, the one number to show, and where it comes from. Read `19` first; numbers marked **[running]** are filled in from the overnight runs (`10`, newest entry, says when they finished). Figures: `paper/fig_reliability.png`, `paper/fig_pilot.png`.

---

**Slide 1 — What we did.**
"We reimplemented Refine4LLM with an open model (`gpt-oss:120b`), Z3 for the search, and Coq and Lean 4 to re-check every finished derivation. Then we asked a question the paper does not answer: if you run it again, does it still work?"

**Slide 2 — One run is not a result.** *(figure: `fig_reliability.png`)*
Square root, the paper's own example: 7 / 10 at first, 99 / 99 after the fixes, and **100 / 100 with the final code** (95 % interval 96–100 %), two model calls in the median run, every derivation re-checked by Coq. The jump is far beyond noise (Fisher exact test, p = 0.0006). Medium reasoning effort: 20 / 20 as well.
*Say:* "The prompt did not change between 7/10 and 29/30; what changed is what the system tells the model after a failed step."

**Slide 3 — Why runs failed (the main idea).**
Ten failure classes read from transcripts (`20`, Table 1). Three to name:
* advice sent to the wrong step (the loop body was told to fix the invariant it cannot change);
* a sub-goal that could never be solved (fixed by checking that every sub-specification is *feasible*);
* **the model was shown a different formula from the one the prover checked** (`2 * (n / 2)` displayed as `2 * n / 2`).
*Say:* "Every fix is a general rule in the engine, none is about the square root."

**Slide 4 — It generalises, and it is sound.**
The other 11 benchmark problems, 20 runs each, final code: **all 11 at 20 / 20 (220 / 220)**, every derivation Coq-certified — including integer division, which was 1 / 20 before the two-assignment search. An impossible specification: never "proved" (0 / 5).

**Slide 5 — The provers disagreed (a finding for the paper's pipeline too).**
Z3 divided −7 / 2 differently from Coq, Lean and Python; Z3 treated arrays of floats as integers; Z3 accepted `b := 0` for a Boolean. All aligned, all pinned by tests. *Ask Dr. Hou:* which division does `L_spec` mean? (`18`, question 5)

**Slide 6 — HumanEval: the honest picture.** *(figure: `fig_pilot.png`)*
* The models alone: `gpt-oss` **156 / 147**, `qwen3-coder-next` **154 / 147** (original / EvalPlus) — above the paper's GPT-4 (145 / 128), close to Refine4LLM (150 / 150).
* Refinement on 20 problems our language can state, with specifications checked against the reference solutions on every test input (590 / 590 wrong answers rejected), 121 runs: **the simple problems every time** (6 problems derived in every run, two model calls each), **loops and searches rarely** — although hand derivations exist for 17 of the 20. 41 runs give a verified program that passes every test, **all 41 certified by Coq**.
* A real win: `multiply`, which the model alone gets wrong on EvalPlus, was derived once (in 8 runs) as a verified program that passes every test.
* Every derived program that runs passes both the original and the EvalPlus tests — the paper's "no drop on EvalPlus" claim, on our subset.
* Nine derived programs were valid proofs that **cannot run** (a proof-only name `V0` in a test; eight quantified values). Only running the programs found this; fixed in v9.
*Say:* "Today the value of refinement is the guarantee, not more passing tests — and with an untuned model it is reliable only for simple problems."

**Slide 6b — Defence in depth (the honest highlight).**
In one HumanEval run the search prover (Z3) accepted a step that is false. **Coq refused to certify it, and the program failed the tests.** One case among roughly seven hundred derivations, not reproducible offline (thousands of retries refute or give up), under investigation. *Say:* "This is why we certify every derivation with an independent proof kernel: we count a derivation as verified only when Coq or Lean has checked it."

**Slide 6c — A termination gap, and its repair.**
Under the paper-style rule (the measure only has to decrease), the model's `gcd` loop `while g is not a common divisor: g := g + 1` with measure `a − g` was accepted — and never stops when `a` does not divide `b`. Over the naturals that rule is enough; over the integers it is not. Every success we count has a bounded measure (265 loops checked with Z3). The repair: also require *"the measure is never negative while the loop runs"* — sound, and the paper's own measure `N − (x+e)²` still passes. *Ask:* are the paper's measures naturals? This decides D1.

**Slide 7 — What the assist does, and does not do.**
Without the leaf assist the model picks the right loop and then answers the trivial set-up (`x := 0`) with another loop: **8 / 30 (27 %)** without it vs 99 / 99 with it (v6 code). The assist proposes only; every step it takes is proved like the model's. *Say:* "It plays the role of the paper's instruction tuning for the boring steps."

**Slide 8 — What we need from you.**
1. The HumanEval formal specifications and the law library (to reproduce Table 6 exactly).
2. Fig. 2's invariant needs `x ≥ 0` for termination: abbreviation, partial correctness, or a different variant rule?
3. Division semantics, quantified guards, Booleans in `L_spec`.
4. The termination rule to make default: strict (`0 ≤ V < V0`; costs one model call per run, 46 / 48 vs 99 / 99, not significantly different), or relaxed plus "the measure is never negative while the loop runs" (sound, admits the paper's measure).

---

### If asked…

| Question | Answer, with evidence |
|---|---|
| "Isn't 99/99 tuned to the square root?" | The same code: all 11 other problems at 20 / 20 (twice); the HumanEval specifications were written without looking at model runs (`14` §5e, `16`). |
| "Is the assist cheating?" | It only proposes; every step goes through the same prover; results with and without it are reported (`14`). |
| "Do the proofs hold outside Z3?" | Coq certified every successful square-root derivation; Lean certifies all 21 obligations of the classic programs (`15`, `16` §6). |
| "Why only 20 of 164?" | The specification language has no strings, list results or `sum`/`len`; that is a language extension, and the paper's own specifications are not public (`16` §3). |
| "Can you show it live?" | Not today: the model server's tunnel reached its monthly bandwidth limit on the morning of 2026-10-05. Show the offline replay in `19` §8 (stored replies through the engine, Coq re-checking each step); live: `python main.py --case C5-sqrt-paper --config gpt-oss-120b-low --assist --certify coq lean` once the limit resets. |
