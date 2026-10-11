# 01 — The Big Picture: what FormalLLM is and why it exists

> **Read this first.** It assumes you know some programming (Python), and *nothing* about formal methods.
> Every new word is explained the first time it appears. File and line references look like
> `path:line` and point into this repository; line numbers drift as the code changes, so treat
> them as "look near here".

---

## 0. Two honest statements up front

1. **FormalLLM is a re-implementation, not original research.** The README says so itself
   (`README.md:3`): it is an independent implementation of the paper
   *"Automated Program Refinement: Guide and Verify Code Large Language Model with Refinement
   Calculus"* — the tool in that paper is called **Refine4LLM**. The paper PDF is in
   `Dr. Hou's Studies/`.
2. **The one big difference from the paper: the prover.**
   Refine4LLM is built on **Coq** (a *proof assistant*) plus **CoqHammer** (a tool that
   calls automatic provers) — the paper says so in §9.1.3: *"We implement our approach based on Coq,
   CoqHammer, and GPT-4. The automatic verification is based on … CoqHammer"*, which in turn
   calls the provers cvc4, Vampire, E and Z3.
   **FormalLLM replaces all of that with a single tool: Z3**, an *SMT solver*
   (`FormalLLM/verification/z3_backend.py`). There is **no Coq and no Lean anywhere in this
   repository's code** (I searched). Where Coq/Lean come in is: (a) the paper's *language* L_spec is
   described as "a subset of the language of Coq", and (b) they are the natural next step if you
   want stronger guarantees — see `02_*`/`03_*` reading files for what those tools are.

If you remember only one sentence: **FormalLLM lets an LLM *steer* a program-construction
process, while a mathematical checker (Z3) *vets every single step*, so the final program is
correct by construction instead of "looks right".**

---

## 1. The problem: LLM code is plausible, not proven

Ask a language model: *"write a function that returns x with x·x ≤ N < (x+e)·(x+e)"*
(a square root accurate to within `e`). You get Python that *usually looks right*. But:

* The model has no idea whether it is right. It predicts likely text.
* Testing only checks the inputs you thought of. `N = 0`? `e` tiny? `e` huge? A subtle off-by-one
  survives until production.
* In safety-critical software (medical, aviation, finance) "usually right" is not acceptable.

**Formal methods** is the field that answers: *can we prove, mathematically, that a program meets
its specification — for all inputs, not just the tested ones?* The catch has always been that
proofs are laborious and need experts. LLMs are the opposite: cheap, creative, unreliable.

### The neuro-symbolic idea ("neuro" = neural network, "symbolic" = logic/maths)

Let each side do what it is good at:

| Side | Good at | Bad at |
|---|---|---|
| **LLM** (neural) | Having *ideas*: "this needs a loop that starts at 0 and adds `e`" | Being *certain*; it hallucinates |
| **Z3** (symbolic) | Checking a logical statement *exactly and for all inputs* | Having ideas; it can't invent a loop invariant |

So the LLM *proposes* a small step, Z3 *checks* it, and only checked steps are kept.
The correctness guarantee never depends on the LLM being right — only on Z3 and on the
(small, human-written, testable) engine code being right. Bad LLM ideas are *rejected, not trusted*.

---

## 2. The method in one picture: stepwise refinement

Instead of asking for the whole program at once, we start from a **specification** (a precise
statement of *what* is wanted, no *how*) and repeatedly **refine** it — replace it with something
closer to real code — until only executable code is left. This is called the **refinement
calculus** (Morgan; see `08a_Refinement_Calculus_Explained.md` for the full story).

```
        specification  (what we want)                      "Spec"
              │   refine   (apply a LAW, with parameters the LLM chose)
              ▼
   ┌──────────┴───────────┐
 smaller spec          smaller spec                        each is a new job
   │ refine                │ refine
   ▼                       ▼
 code: x = 0         code: while ...: x = x + e            "program"
              │
              ▼
      whole program, assembled from the leaves          → Python
```

A **law** is a pre-proved recipe like "to meet a spec, you may do *A then B*, **provided** some
logical condition holds". The condition is the **proof obligation**. The engine hands it to Z3.
The LLM's job is to *choose which law* and *fill in its blanks* (the **parameters**: a midpoint,
a loop guard, a loop invariant…). The blanks are the hard, creative part.

---

## 3. The architecture, in plain words

(The README has a fancy Mermaid diagram at `README.md:14`; here is the human version.)

```
 you write                      ┌────────────────────────────────────────────────────────┐
 a SPEC  ──► parser ──► Spec ───►   AutomatedRefiner  (the "control loop")               │
 (L_spec)   lspec/parser.py     │   agent/refiner.py                                      │
                                │      │                          ▲                      │
                                │ 1. build prompt          6. failure message           │
                                │      ▼                          │  (counterexample)    │
                                │   LLM (llm/provider.py)         │                      │
                                │      │  "law + parameters" JSON │                      │
                                │ 2. parse (llm/parser.py)        │                      │
                                │      ▼                          │                      │
                                │   RefinementEngine ── apply law ─► sub-specs + OBLIGATIONS
                                │   refinement/engine.py          │                      │
                                │      │ 3. each obligation       │                      │
                                │      ▼                          │                      │
                                │   Z3 backend ───────────────────┘                      │
                                │   verification/z3_backend.py                           │
                                │      │ PROVED → keep  /  FAILED → reject               │
                                │ 4. recurse on each sub-spec (new node in the graph)    │
                                └──────┼─────────────────────────────────────────────────┘
                                       ▼ 5. when all leaves are code
                       RefinementGraph.reconstruct_program()  → LPL program AST
                       lpl/to_python.py → Python text  → execution/runner.py (tests)
```

Vocabulary you will see everywhere:

| Term | Meaning | Where |
|---|---|---|
| **L_spec** | The specification language (logic: ∧, ∨, ¬, ∀, ∃, arithmetic, arrays) | `FormalLLM/lspec/` |
| **L_pl** | The tiny programming language that refinement ends in: `:=`, `skip`, `;`, `if`, `while` | `FormalLLM/lpl/ast.py` |
| **L_mix** | Programs that still contain unrefined specs as holes — the in-progress state | `lpl/ast.py:MixNode` |
| **Precondition (P)** | What is true *before* the program runs | `Spec.precondition` |
| **Postcondition (Q)** | What must be true *after* | `Spec.postcondition` |
| **Frame** | Which variables the program is allowed to change; all others are "rigid" | `Spec.frame`, `refinement/frame.py` |
| **Law** | A verified refinement recipe | `refinement/laws/*.py` |
| **Proof obligation** | A logical claim that must hold for a law to be valid | `verification/proof_obligations.py` |
| **Z3** | An SMT solver: decides whether a claim is valid, or gives a counterexample | `verification/z3_backend.py` |
| **Refinement graph** | The bookkeeping record of every node (spec) and attempt (law tried) | `refinement/graph/` |

---

## 4. End-to-end walkthrough: the square-root example

This is the paper's motivating example (Figures 2–3) and the repo's case `C5-sqrt-paper`
(`benchmarks/cases.py`). I actually ran the engine on it to get the real strings below
(they are the same moves as the regression test `FormalLLM/tests/test_engine_reachability.py:48`).

### Step 0 — the specification

You write (L_spec syntax, grammar in `FormalLLM/lspec/grammar.lark`):

```
Frame: x.
Precondition:  (N:float)(e:float) := N >= 0 /\ e > 0.
Postcondition: (N:float)(e:float) := x*x <= N /\ N < (x+e)*(x+e).
```

Read it as: *"Given a non-negative `N` and a positive tolerance `e`, set the variable `x`
(only `x` may change — that's the **Frame**) so that `x² ≤ N` and `N < (x+e)²`."* `N` and `e` are
inputs that never change. This is Morgan's notation `x : [ N≥0 ∧ e>0 , x²≤N ∧ N<(x+e)² ]`.

`parse_spec` (`lspec/parser.py:128`) turns the text into a `Spec` dataclass tree (`lspec/ast.py:50`).

### Step 1 — the refiner asks the LLM

`AutomatedRefiner.refine_node` (`agent/refiner.py:67`) builds a prompt
(`llm/prompts.py:92`, `generate_state_prompt`) containing: the spec, a statement of the frame
("You may ONLY assign to: x"), the list of laws with their parameters, a syntax cheat-sheet, and
— on retries — the history of earlier failures. It demands JSON like
`{"law": "...", "parameters": {...}, "rationale": "..."}`.

A good model (in the repo's logs only `gpt-oss-120b` managed this end to end — see
file 08a §"What the experiments show") answers roughly:

```json
{"law": "initialised_iteration",
 "parameters": {"invariant": "x*x <= N && x >= 0",
                "guard":     "N >= (x + e)*(x + e)",
                "variant":   "N - x*x"}}
```

The idea behind it: *"Start x at 0. Keep adding `e` while doing so doesn't overshoot √N. When the
loop stops, x is within `e` of the root."* The LLM supplied three creative things:

* **invariant** `x*x <= N ∧ x >= 0` — a fact that is true before the loop and stays true after each
  iteration ("x hasn't overshot yet").
* **guard** `N >= (x+e)²` — keep looping while a step is still safe.
* **variant** `N − x²` — a quantity that must get strictly smaller (and stay ≥ 0) each pass,
  which *proves the loop terminates*.

`parse_llm_response` (`llm/parser.py:157`) extracts the JSON (tolerating messy model output) and
`parse_expr` (`llm/parser.py:58`) turns the strings into L_spec expressions — it even rewrites `&&`
and `==` into `/\` and `=` because backslashes break JSON (`llm/parser.py:16-40` explains the measured
failure that motivated this).

### Step 2 — the engine applies the law and builds obligations

`RefinementEngine.apply` (`refinement/engine.py:26`) looks the law up in the registry
(`laws/registry.py:28`), calls `InitialisedIterationLaw.apply`
(`laws/initialised_iteration.py:23`), and gets back a `RefinementResult` containing

* **one proof obligation**: *on loop exit, invariant ∧ ¬guard ⇒ postcondition* — i.e.
  `(N≥0 ∧ e>0 ∧ x²≤N ∧ x≥0) ∧ ¬(N ≥ (x+e)²)  ⇒  x²≤N ∧ N < (x+e)²`;
* **two sub-specifications** (real output of the run):

```
init  :  PRE  N>=0 /\ e>0
         POST (N>=0 /\ e>0) /\ (x*x <= N /\ x>=0)              "establish the invariant"

body  :  PRE  (N>=0 /\ e>0) /\ (x*x<=N /\ x>=0) /\ N >= (x+e)*(x+e) /\ (N - x*x) = (N0 - x0*x0)
         POST (N>=0 /\ e>0) /\ (x*x<=N /\ x>=0) /\ 0 <= N - x*x /\ N - x*x < N0 - x0*x0
                                                              "preserve the invariant, shrink the variant"
```

Notice `N0`, `x0`: the suffix `0` means "the value *before* the body ran". `V = V0` in the body's
precondition simply remembers the variant's starting value so the postcondition can say it
decreased. Also notice `N>=0 /\ e>0` was **carried into** both sub-specs automatically — that is the
**frame** machinery (`refinement/frame.py:85`, `rigid_context`): since `N` and `e` are not in the
frame they can never change, so facts about them stay true everywhere. Without it Z3 would
consider `e ≤ 0` inside the loop body and reject a correct answer (the docstring at
`frame.py:1-25` records that this happened to `gpt-oss-120b`).

### Step 3 — Z3 checks the obligation

`verify_obligation` (`verification/z3_backend.py:58`) does the classic trick: to prove
`A ⇒ B`, ask Z3 whether `A ∧ ¬B` is **satisfiable**.

* **unsat** (no counterexample exists) → the implication is valid → `PROVED`.
* **sat** → Z3 found values making A true and B false → `FAILED`, plus a **counterexample**
  (e.g. `x = -2`). `describe_failure` (`z3_backend.py:12`) turns it into advice the LLM can act on.
* **unknown** → Z3 gave up (timeouts, hard nonlinear arithmetic) → `INCONCLUSIVE`. Note this
  example has `x*x` (nonlinear), which is exactly where Z3 can struggle.

If any obligation is `FAILED`/`UNKNOWN`, the engine raises `VerificationError` and the refiner
records the attempt as rejected; the counterexample is fed back into the next prompt.

### Step 4 — recurse on the sub-specs

The refiner creates a graph node for each sub-spec (`graph.create_node`,
`refinement/graph/graph.py:24`) and calls `refine_node` on each.

* `init` → the LLM picks `assignment` with `x := 0`. Obligation: `P ⇒ Q[x:=0]`, i.e.
  `N≥0 ∧ e>0 ⇒ 0*0 ≤ N ∧ 0 ≥ 0 ∧ …`. Z3: proved. This node is now *terminal* (it yields code).
* `body` → `assignment` with `x := x + e`. Obligation: the whole body postcondition with `x`
  replaced by `x+e`; its assumption includes the loop guard `N ≥ (x+e)²`, which is exactly what makes
  `(x+e)² ≤ N` hold. Z3: proved. (I ran this: it is proved.)

If a sub-spec *can't* be refined within its retry budget, the refiner backtracks: it marks the
parent attempt `ABORTED`, tries other parameters, and eventually blacklists the law for that node
(`agent/refiner.py:41-140`, see file 07).

### Step 5 — reassemble and emit Python

Each law knows how to put its children back together (`build_program`, e.g.
`initialised_iteration.py:84` returns `SequentialComposition(init, While(guard, body))`).
`RefinementGraph._assemble` (`graph.py:114`) folds the tree bottom-up into an L_pl AST, and
`to_python` (`lpl/to_python.py:43`) prints:

```python
x = 0
while (N >= ((x + e) * (x + e))):
    x = (x + e)
```

(The test asserts the first line is `x = 0`, `test_engine_reachability.py:67`.)

### Step 6 — run it (sanity, not proof)

`execution/runner.py:10` executes the code in a **separate Python process** against test cases and
the postcondition. Remember the *proof* already happened in step 3–4; this is a belt-and-braces
check that the Python translation behaves (see "Common confusions" for why that matters).

### The whole run as a timeline

```
Spec ─► LLM: initialised_iteration(inv, guard, variant)
          └► Z3: exit obligation          PROVED
          ├─► sub-spec "init" ─► LLM: assignment x:=0       ─► Z3 PROVED ─► code
          └─► sub-spec "body" ─► LLM: assignment x:=x+e     ─► Z3 PROVED ─► code
all leaves are code  ─►  x=0; while ...: x=x+e   ─►  Python  ─►  run tests
```

---

## 5. What makes this *robust* (the work in progress)

The "making it robust" thread in this repo is mostly about the **seams** between the fuzzy LLM and
the exact engine. Real examples already in the code:

* **JSON/backslash mangling** of `/\` — normalised in `llm/parser.py:16-60`.
* **Lost context** (rigid facts dropped from sub-specs) — fixed by frames (`refinement/frame.py`).
* **Non-progress loops** (a law that returns the same spec forever) — progress guard in
  `agent/refiner.py` (`spec_key`, depth limit, tests in `tests/test_progress_guard.py`).
* **Uninformative failure messages** — `describe_failure` now says *what* failed and suggests
  strengthening the invariant (`z3_backend.py:12-44`).
* **Z3 hanging forever** — a timeout was being added (`z3_backend.py:47-65`, env var
  `FORMALLLM_Z3_TIMEOUT_MS`; this change is uncommitted in the working tree as I write).
* **Open issue #3** on GitHub: models can pick the right *law* but fail to write the right
  *parameters* (invariants!) — the central weakness; see `08a_*` for the data.

---

## 6. Common confusions

**"Z3 proves the program correct, so the Python must be correct."**
Z3 proves the *refinement steps*, in mathematical arithmetic (`Int`/`Real` in
`lspec/z3_translator.py:8-15`). Python uses finite floats and `int`. A program proved correct over
the reals can misbehave with float rounding, and `/` in generated Python is true division regardless
of types (`to_python.py:5-20` only renames `/\ \/ = <>`). So "verified" here means *correct with respect to
the logic's model of arithmetic*; the execution tests are a cheap guard on the gap.

**"The LLM writes the program."**
No. In the `refinement` arm the LLM never writes code; it picks laws and parameters, and the code is
*emitted from the verified tree* (docstring of `benchmarks/evaluate_models.py:1-20`). That is the whole
point of the study comparing it with the `direct` arm, where the LLM writes the Python itself.

**"Refinement = rewriting code."**
Here "refine" means *make a specification more concrete*, preserving the guarantee
("every behaviour of the result is allowed by the original spec"). It starts from specs, not code.

**"Proof obligation = test."**
A test checks one input. An obligation is a logical statement about *all* inputs; Z3 either proves
it or hands back a witness.

**"A precondition is checked at runtime."**
Not here. It is an *assumption* the proofs may use; the caller is responsible for it.

**"If Z3 says unknown, the step is probably fine."**
No — `UNKNOWN` is treated as failure (`engine.py` raises; refiner records `INCONCLUSIVE`).

**"This is the same as Dafny / Coq program extraction."**
Related idea (correct-by-construction), different machinery. Refinement calculus *derives* the
program from the spec; Dafny *verifies* a program you wrote.

---

## 7. Check yourself

1. In your own words: what is the division of labour between the LLM and Z3? Which of them could you
   remove while still getting a *correct* (but maybe useless) result? *(Hint: remove the LLM → nothing
   proposes steps; remove Z3 → nothing is trustworthy.)*
2. Why does the engine ask Z3 whether `A ∧ ¬B` is satisfiable, rather than `A ⇒ B`?
3. In the sqrt example, what are the three things the LLM must invent for `initialised_iteration`?
   Which of the three guarantees termination?
4. What does the suffix `0` mean in `x0`? Why does the body's precondition contain `V = V0`?
5. Why does `e > 0` need to be carried into the loop body, and what makes that sound?
6. Name two ways code verified by Z3 can still misbehave when run in Python.
7. What does the paper use instead of Z3 directly, and what do those tools have in common with Z3?
8. *Explain why an LLM that proposes a *wrong* invariant cannot make the system output a wrong program.*

*Answers sketch:* (2) Z3 searches for *counterexamples*; unsat means none exist. (4) value before the
body ran; to state "variant decreased". (5) `N`,`e` aren't in the frame so can't change; (8) the
`exit` obligation or the body's obligation fails, so the step is rejected.

**Next:** `07_Codebase_Tour.md` (where everything lives) and `08a_Refinement_Calculus_Explained.md`
(the theory + the study results).
