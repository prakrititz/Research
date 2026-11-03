# 11 — The Paper Explained (Refine4LLM)

> **Paper:** *Automated Program Refinement: Guide and Verify Code Large Language Model with Refinement Calculus* — Yufan Cai, **Zhé Hóu**, David Sanan, Xiaokun Luan, Yun Lin, Jun Sun, Jin Song Dong (preprint, Nov 2024, 36 pages). The PDF is in `Dr. Hou's Studies/`. Zhé Hóu is a co-author; the folder name suggests this is your professor's work.
>
> **Purpose of this file:** so that you and I read the paper *the same way*, before we change any code. Every number and quote below was taken from the PDF text. Where I am **interpreting** rather than quoting, I say "my reading". Page numbers refer to the PDF's own page numbers, so you can open the PDF next to this file.
>
> Next file: `12_Paper_vs_Our_Implementation.md` (where our code agrees with the paper and where it does not).

---

## 0. If you only read one section: the 8 facts

1. **The goal** is *verified* code from an LLM: "(1) formally refine the specifications, (2) automatically prompt and guide the LLM using refinement calculus, (3) interact with the LLM to generate the code, (4) verify … thus guaranteeing its correctness, (5) learn and build more advanced refinement laws" (abstract, p.1).
2. **The LLM is treated as a "constraint solver"**, not as an oracle. The system asks it narrow questions ("pick a law", "write code satisfying this formula") and a theorem prover checks every answer (§1 p.3, §8.2 p.17).
3. **Who produces what is fixed by Table 5 (p.16).** For the iteration law the LLM supplies only an **invariant I** and a **guard G** — *not* a variant. The system builds everything else. (§3 below.)
4. **The loop is Algorithm 1 (p.34):** LLM picks a law → system derives the *condition* → LLM writes code/parameters for that condition → prover verifies → if it fails more than **5** times, **fall back** to the previous step.
5. **The prover is Coq + CoqHammer** (which calls cvc4, Vampire, E and Z3) — §9.1.3 p.19. *Not Z3 alone.*
6. **The LLM is GPT-4, instruction-tuned** on Morgan's refinement examples and on the extended laws (§8.2 p.17, §9.1.3 p.19). *Not a zero-shot small model.*
7. **The headline result (Table 6, p.19):** 150 / 164 programs pass on both HumanEval and EvalPlus, versus 145 / 128 for plain GPT-4 given only English. The point: *the pass rate does not drop on the harder EvalPlus tests*, because the code is verified.
8. **The square-root example is an illustration**, not a benchmark row. The paper shows a success run, a failure run and a binary-search run (Figs. 2, 3, 4, 9) but reports **no success-rate number for sqrt**.

---

## 1. The problem (paper §1, Fig. 1, p.2)

Prompt: *"Find the square root of N within the error bound e."* Three famous tools produce almost-right, actually-wrong programs:

| Tool | What went wrong |
|---|---|
| GitHub Copilot | wrong upper bound when N < 1 (needs `high > N + 1/4`) |
| GPT-4 | for e.g. `sqrt(5)`, `x` hits a floating-point *fixed point* and the loop never ends |
| OpenAI o1-preview | `x` initialised to a *negative* number → wrong answer when N is tiny |

So: LLM code is *plausible* but unverified, and the process is a black box. The authors cite a result that hallucination cannot be removed "by simply changing the prompts" (§1 p.3). Their answer is **not a better prompt**; it is to **check every step with a prover**.

> **Note for you:** this matters for how to read your professor's comment "the prompt is wrong". The paper's own claim is that prompting alone cannot fix correctness — the *prover* does that. Prompts matter for **efficiency** (fewer wasted attempts), not for correctness. Keep that distinction in mind.

---

## 2. The method in one picture

```
                    ┌────────────────────────── INFORMAL (LLM) ──────────────────────────┐
 formal spec        │                                                                     │
  x:[pre,post] ───► │  ① "Choose a proper rule to refine [pre,post]"  → law              │
                    │  ③ "Given the rule … write code/parameters"     → code / I,G / M … │
                    └─────────────┬──────────────────────────────────────▲───────────────┘
                                  │ law                                   │ counterexample
                    ┌─────────────▼───────────────  FORMAL (ATP)  ────────┴───────────────┐
                    │  ② system derives the CONDITION (proof obligation scheme)           │
                    │  ④ builds Coq script → CoqHammer / ATPs verify                      │
                    │  ⑤ ok → new sub-specifications; Save(code)                          │
                    │     not ok → FailCount++ ; if FailCount > 5 → FallBack             │
                    └─────────────────────────────────────────────────────────────────────┘
        repeat on every remaining sub-specification until only program code is left
```
(Circled numbers = lines 6–16 of Algorithm 1.)

Two things to notice:
* **Law choice and parameters are two different LLM calls** (line 6 `law ← LLM(spec)`, line 8 `code ← LLM(spec, law, condition)`). The `condition` is computed *by the system* between them and shown to the LLM. That is "actively guiding": the LLM sees the exact logical statement it must satisfy.
* **No history is needed** in the prompt: each sub-spec is self-contained, by the congruence of Hoare logic (§8.2 p.17).

---

## 3. Table 5 — who produces what (p.16) ★ most important table

| Law | The LLM provides | The system (Refine4LLM) does |
|---|---|---|
| Skip | — | verify `P ⇒ Q` |
| Sequence | `M` (a middle formula) | new specs `[P,M]` ; `[M,Q]` |
| Assignment | `x = Expr` | verify `P ⇒ Q⟨x:=Expr⟩` |
| Alternation | `G` (a guard formula) | new specs `if G then x:[P∧G,Q] else x:[P∧¬G,Q]` |
| **Iteration** | **`I` (invariant), `G` (guard)** | new specs `x:[P,I]` ; `while G do x:[I∧G, I∧(∃i<M, Vᵢ→¬G)]` |
| Traverse | `P` | builds an array-traversal loop |

**Read the Iteration row twice.** The LLM is asked for **two** formulas, I and G. The *variant* (the quantity that proves the loop ends) is **not** something the LLM writes: §10.1 says *"The invariant, the guard condition, and the variant can be extracted from the specification."* (my reading: once the middle formula of a sequence is chosen, the remaining spec has the shape `[Inv, Inv ∧ ¬G]`, so G is "the negation of the second conjunct" and the variant is read off the guard.)

Compare how the paper *describes* the sqrt iteration step (§3.1, p.6): *"Refine4LLM will use the constraints 'Invariant ∧ Guards → Invariant ∧ Variant is strictly decreasing' as a prompt and instruct the LLM to generate code like `x = x + e`."* So for the loop **body**, the LLM writes *code*, and the system checks that code against that constraint.

---

## 4. The laws

### 4.1 Core laws (Morgan; §2.2 pp.4–5)
`x : [pre, post]` reads: *"starting in a state satisfying `pre`, change only the variables `x`, and finish in a state satisfying `post`."* A program `S1` *refines* `S0` (`S0 ⊑ S1`) if it is correct wherever `S0` is (via weakest preconditions, eq. 1 p.4).

| Lemma | Law | Rule |
|---|---|---|
| 2.1 | Strengthen postcondition | if `post' ⇒ post` then `[pre,post] ⊑ [pre,post']` |
| 2.2 | Weaken precondition | if `pre ⇒ pre'` then `[pre,post] ⊑ [pre',post]` |
| 2.3 | Skip | if `pre ⇒ post` then `[pre,post] ⊑ skip` |
| 2.4 | Sequential | `[pre,post] ⊑ [pre,mid] ; [mid,post]` |
| 2.5 | Assignment | if `pre ⇒ post⟨x:=E⟩` then `[pre,post] ⊑ x = E` |
| 2.6 | Alternation | `if ⋁ᵢ Gᵢ then [Gᵢ ∧ pre, post]`, requires `pre ⇒ ⋁ᵢ Gᵢ` |
| 2.7 | Iteration | `x:[Inv, Inv ∧ ¬GG] ⊑ while GG do x:[Inv ∧ Gᵢ, Inv ∧ (0 ≤ V < V₀)]` with `V` **integer-valued** |
| 2.8 / 2.9 | Expand / Assertion | add a variable / insert `assert E` |
| 2.11 / 2.12 | Procedures | call-by-value / result |

### 4.2 Extended laws (§6.2 pp.13–14) — *why they exist*
They were **learned** from refinement trees: the authors noticed the same shape recurring ("sequence, then assignment for the first half, then iteration for the second") and packaged it. Benefits they claim (§3.4 p.8): *"broaden the horizon of the LLM from one-step refinement to considering future directions"*, *"reduce the depth of refinement"*, *"simplify program verification"*.

| Lemma | Law | Idea |
|---|---|---|
| 6.1 | Initialised skip | may assume `x = x₀` |
| 6.2 | Flexible sequential | `[P,Q] ⊑ [A,B];[C,D]` given `P⇒A`, `B⇒C`, and the paper writes `Q⇒D` (its own proof actually needs `D⇒Q`; our code uses `D⇒Q`) |
| 6.3 / 6.4 | Initialised / following assignment | assignment with `x=x₀` facts; or "set up then assign" |
| 6.5 | If-else alternation | `if G then [P∧G,Q] else [P∧¬G,Q]` — no `G∨¬G` obligation needed |
| **6.6** | **Initialised iteration** | `x:[P, I∧¬G] ⊑ x:[P,I]; while G do x:[I∧G, I∧(∃i<M, Vᵢ→¬G)]` |
| **6.7** | **Assertion iteration** | same, but body is `x:[I∧G, I∧V<V₀]; assert V≠V₀` — *the variant needs no lower bound; a runtime assertion catches float fixed points* |
| 6.8 | Traverse | array loops `i = m … n` |

**Two details that will matter later:**
* In 2.7 (core) the variant satisfies `0 ≤ V < V₀` and is integer-valued. In 6.6/6.7 the paper **drops the integer/lower-bound requirement**: *"we replace the condition for integer-valued variants with any variant expression for scalability"* (p.14) and, for floats, uses *"the monotonic and bounded condition"*, adding the assertion *"to avoid infinite loops"*.
* §11.3 (p.27) openly says: *"One limitation … is the lack of proof for loop termination in some cases. If a refinement lacks such proof, we still consider the program partially correct."*

---

## 5. The square-root story (§3, Figs. 2, 3, 4, 9)

Spec (Fig. 9, p.22): `pre: N ≥ 0 ∧ e > 0`, `post: x*x ≤ N < y*y ∧ y ≤ x+e` (two variables `x`,`y`; binary search). The simpler one-variable form (Figs. 2–3): `post: x*x ≤ N < (x+e)*(x+e)`.

**Success (Fig. 2, p.6)** — I extracted the figure image from the PDF and read it directly, so these are the exact formulas:

```
x:[ N≥0 ∧ e>0 ,  x² ≤ N < (x+e)² ]
   │ LLM: sequential composition   (middle condition:  x² ≤ N )
   ├─ x:[ N≥0 ∧ e>0 , x² ≤ N ]            LLM: assign  x = 0          → ATP verify → success
   └─ x:[ x² ≤ N , x² ≤ N < (x+e)² ]
        │ LLM: iteration      Invariant:  x² ≤ N        Guard:  N ≥ (x+e)²
        └─ x:[ x² ≤ N ∧ N ≥ (x+e)² ,  x² ≤ N ∧ (N − (x+e)²)↓ ]
              LLM: assign  x = x + e                                 → ATP verify → success
```
Three things to notice: **(1)** the middle condition and invariant are just `x² ≤ N` — **no `x ≥ 0`**; **(2)** the guard is `N ≥ (x+e)²`, and the variant `N − (x+e)²` is simply *read off the guard*; **(3)** the loop body's postcondition says only "the variant is decreasing" (`↓`) — **there is no `0 ≤ V` lower bound**.

> ⚠ **A point to raise with Dr. Hou.** When I replay exactly this chain against our engine, the last step (`x = x + e`) is rejected in *both* termination modes, with the counterexample **x = −3, e = 1, N = 10**: here `x² = 9 ≤ N` and `(x+e)² = 4 ≤ N` hold, but after `x = −2` the variant `N − (x+e)²` goes from 6 *up* to 9. The invariant `x² ≤ N` does not forbid negative `x`, and for negative `x` stepping by `+e` can move *toward* zero and make `N − (x+e)²` grow. The step is accepted only if the body is required to **preserve the invariant alone** (partial correctness), which is consistent with §3.1's remark that the check is "partially correct" and §11.3. Question for Dr. Hou: *what exactly does the ATP check for the loop body in Fig. 2 — is the "↓" a proof obligation, or a note?* (This is the same negative-`x` trap the paper blames on o1-preview in Fig. 1.)

**Failure (Fig. 3, p.7), §3.2 — this is the "failure feedback" the paper advertises.** Here the sequence's middle condition is `N < (x+e)²` (the *other* conjunct), so the loop must start from a large `x` and shrink it (invariant `N < (x+e)²`, guard `N < x²`):
1. LLM tries to initialise `x = N` → prover **rejects** (dashed arrow = feedback to the LLM), gives a counterexample; per the text the LLM retries until it reaches `x = N + 1` (accepted).
2. Next the body `x = x − e` → prover **rejects**: the variant `x² − N` is *not* strictly decreasing in some cases (eq. 3).
3. LLM tries Newton's `x = (x + N/x)/2` → rejected: the variant stalls at a **floating-point fixed point**.
4. After repeated failure the system **traces back** to the last good step and chooses a *different law*.

So the paper itself shows that the *choice of middle condition* (`x² ≤ N` vs `N < (x+e)²`) decides whether the rest is easy (Fig. 2) or a dead end (Fig. 3).

**Binary search (Fig. 4/9, §10.1).** (Fig. 4 prints the postcondition with `y < x+e`; Fig. 9 with `y ≤ x+e` — a small inconsistency in the paper.) Sequence → `x = 0; y = N+1` (note: `y = N` would be rejected because `N < y²` fails for small N) → iteration (invariant `x² ≤ N < y²`, guard `y > x+e`) → alternation on `((x+y)/2)² > N` → assign `y` or `x` to the midpoint. The termination argument is in Appendix A.3 (Lemmas A.2/A.3) and is a **mathematical proof sketch**, not an ATP run.

> My reading: the sqrt figures show the *mechanism* (propose → verify → counterexample → retry → backtrack). The paper reports no repeat counts, success rate or model comparison for sqrt.

---

## 6. The languages (§5, pp.9–11)

* **L_spec** — "extends first-order logic and is a subset of the language of Coq" (p.10). Types `bool | nat | int | float | char | array<T>`. Operators `∧ ∨ ¬ forall exists < <= = > >= <>`, `+ - * /`, `x0` = previous value of `x`, `a[i]`, `a[i:j]`. Convention: lowercase = variables that change, UPPERCASE = constants.
* **L_pl** — a small imperative language: `pass`, assignment, `;`, `assert`, `while`, `if/else`, `def` procedures. *"straightforward translation … to, e.g., python."*
* **L_mix** — programs where some parts are still specifications (what the tree looks like mid-refinement).

---

## 7. The "informal system" (§8, pp.16–18)

* **Library (top-down / bottom-up):** split a big spec into small ones, look each up in a *library of already-refined specs*, reuse; refine only the new ones; save them back. (This is a major source of the speed-ups in Table 8.)
* **Retrieval-augmented + instruction-tuned LLM:** the refinement calculus is given to the model "as background knowledge"; GPT-4 was **instruction-tuned with the examples in Morgan's book** (p.17, p.19).
* **"Actively guide" prompts**, the paper's own words (p.18):
  > *"Given the refinement rule … The previous code … is not correct since … Provide a correct code satisfying the specification [pre, post]."*
  > *"Choose a proper rule to refine the current specification [pre, post]."* — *"where all the rules are included in the context."*
  > *"Our prompt is relatively straightforward yet comprehensive and includes all the details of the refinement rules and specifications."*

  Observe: **short templates, but all the rule definitions are in the context, and the logical formulas of the current spec are inserted.** Nothing is specific to any one problem.

---

## 8. Results (§9, pp.18–21) — the numbers you should "follow"

**Setup (§9.1):** baselines GPT-4 and CorC (a KeY-based correctness-by-construction IDE). Benchmarks: CorC's classic examples + the 164 HumanEval problems and EvalPlus (same 164, ~80× more tests). Formal specs for HumanEval were adapted from the BigCode project and **manually checked**.

**Table 6 — programs passing all tests (out of 164):**

| | Llama3 | GPT-3.5 | Claude-3 | GPT-4 | GPT-4 + formal spec | **Refine4LLM** |
|---|---|---|---|---|---|---|
| Input | English | English | English | English | English + FS | **FS** |
| HumanEval | 125 | 126 | 136 | 145 | 148 | **150** |
| EvalPlus | 116 | 116 | 126 | 128 | 142 | **150** |

**Table 7 — classic refinement problems (CorC examples):** "Initial" = Refine4LLM with core laws only.

| Problem | Steps: CorC / Initial / Refine4LLM | Proof time (s): CorC / Initial / Refine4LLM |
|---|---|---|
| Linear Search | 5 / 5 / 4 | 0.4 / 0.2 / 0.1 |
| Max Element | 9 / 10 / 5 | 1.2 / 1.0 / 0.2 |
| Pattern Matching | 14 / 16 / 8 | 54.9 / 35.8 / 24.5 |
| Exponentiation | 7 / 7 / 5 | 15.2 / 14.4 / 10.4 |
| Log Approximation | 5 / 5 / 4 | 42.7 / 22.9 / 20.1 |
| Dutch Flag Sort | 8 / 9 / 5 | 5.7 / 4.3 / 4.1 |
| Factorial | 5 / 5 / 3 | 3.6 / 1.5 / 0.4 |

**Table 8 — with vs without the library (50 HumanEval problems with >2 sub-questions, 600 s cap):** steps 21.4 → 5.6; refinement time ~514 → ~275 s; proof time ~215 → ~87 s; **fall-back rate 26.87% → 9.45%**; program size 41.3 → 14.1 lines; pass rate 52% → 82%.

**Table 9 — ablation (EvalPlus):**

| Setting | Pass rate | Refinement time |
|---|---|---|
| Core laws, untuned GPT-4 | 87.8% | 305 s |
| + extended laws | 87.8% | 261 s |
| + instruction tuning | 91.5% | 234 s |
| Full Refine4LLM | 91.5% | 215 s |

**Failure analysis (§9.2.2, p.20) — of the 14 failures out of 164:** 8 specs too complex to split; 3 verification failures (prover too weak); 3 needing data structures the laws don't cover (dictionaries, graphs). (8+3+3 = 14 = 164 − 150 ✓.)

**What these results do and do not tell you** (my reading):
* ✔ Verified refinement *can* beat unguided LLMs on HumanEval-style tasks **with GPT-4 + tuning + Coq/CoqHammer + a library**.
* ✔ Extended laws mostly buy **speed and fewer steps**, and instruction tuning buys **pass rate** (+3.7 points).
* ✘ No result for open-weight small models. ✘ No per-law or per-parameter success rates. ✘ No sqrt success rate. ✘ HumanEval specs are mostly *simple* (the paper itself notes a "hurdle" only for complex ones).

---

## 9. Limitations the authors state (§11, pp.27–28)
1. A human must supply and check the **formal specification**.
2. It "heavily relies on the LLM's ability" for **law selection and code generation**; they warn that *"a complete decoupling of law selection from code generation could result in inefficient or incorrect code generation."*
3. **Termination** is not always proved → "partially correct".
4. **Scalability** is limited by the LLM and the ATPs; more laws needed for separation logic and richer data structures.

---

## 10. Vocabulary check

| Term | Meaning here |
|---|---|
| ATP | automated theorem prover (Z3, cvc4, Vampire, E) |
| CoqHammer | Coq plug-in that sends a goal to several ATPs and reconstructs the proof |
| Proof obligation / "condition" / "proviso" | the logical statement that must hold for a law application to be sound |
| Fall-back | go back to the last verified specification and pick another law |
| Instruction tuning | fine-tuning an LLM on (instruction → answer) examples |
| Variant | a quantity that shrinks every iteration, proving termination |

---

## Check yourself
1. In Table 5, what does the LLM provide for the **iteration** law? What does the system provide? *(I and G; the new specs and the variant condition.)*
2. How many verification failures trigger a fall-back in Algorithm 1? *(More than 5.)*
3. Which prover does the paper use, and which LLM? *(Coq + CoqHammer over cvc4/Vampire/E/Z3; GPT-4 with instruction tuning.)*
4. Does the paper report a success rate for the sqrt example? *(No — it is illustrative.)*
5. Why does the core iteration law require `0 ≤ V`, and why do the extended laws relax it? *(Integer variants cannot decrease forever; floats can, so the paper replaces it with a monotonic-and-bounded condition plus a runtime assertion.)*
6. Why can't a better prompt alone remove hallucination, according to the paper? *(Cited result: hallucination is inevitable; hence the verifier.)*
