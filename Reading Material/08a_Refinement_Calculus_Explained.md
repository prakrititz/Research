# 08a — The Refinement Calculus, from zero (and how this repo implements it)

> Prerequisite: `01_Project_Big_Picture.md`. No prior logic assumed beyond "if–then" and "and/or/not".
> Every law below is explained three ways: **intuition → the rule → exactly what the code does**
> (file:line). Where the code differs from textbook/paper, that is called out.

---

## Part 1 — Foundations

### 1.1 Why logic at all? Preconditions and postconditions

Suppose we want a function for "increment x". We can describe *what it must achieve* without any code:

* **Precondition P** — what we may assume is true at the start. e.g. `x ≥ 0`.
* **Postcondition Q** — what must be true at the end. e.g. `x = x0 + 1` (where `x0` = the starting value of x).

This pair is the core of **Hoare logic** (Tony Hoare, 1969). Writing `{P} program {Q}` means
*"if P holds before the program runs, and it terminates, then Q holds afterwards."*
Hoare logic is for **checking** a program someone already wrote.

### 1.2 Morgan's twist: a *specification statement* is a program-shaped hole

Carroll Morgan's **refinement calculus** turns this around. Instead of checking a program, you write

```
        w : [ P , Q ]          "specification statement"
```

pronounced: *"some program that, started in a state satisfying P, finishes in a state satisfying Q,
**changing only the variables in w**."* `w` is the **frame**. It is a **legal program fragment**
whose body is a promise rather than code. In the repo this is the `Spec` dataclass
(`FormalLLM/lspec/ast.py:50`) and the surface syntax

```
Frame: x.
Precondition:  (N:int) := N >= 0.
Postcondition: (N:int) := x = N + 1.
```

| Morgan | In this repo |
|---|---|
| `w` | `Frame: ...` → `Spec.frame` (`None` means "unknown: anything may change") |
| `P` | `Precondition: … := expr.` → `Spec.precondition.expr` |
| `Q` | `Postcondition: … := expr.` → `Spec.postcondition.expr` |
| `x0` (value before) | written `x0`; grammar token `PREV_STATE` (`grammar.lark:53`); AST `VariablePreviousState` |

Parameters like `(N:int)` are **logical constants** (inputs). They are not in the frame, so they are
**rigid**: no step of the program may change them.

### 1.3 The refinement relation ⊑

`S ⊑ T` ("**S is refined by T**") means: *T can be used anywhere S was promised, and nobody can tell
the difference except that T is more concrete*. Precisely: whenever S is allowed to produce an outcome,
**T's every behaviour is one that S allowed**. T may be *less nondeterministic* (picks one of several
allowed answers) or *more defined* — never *less safe*.

Intuition by analogy: S = "build me something that can carry 100 kg". T = "a steel bridge rated 500 kg".
T refines S. A cardboard box would not.

Two properties give the method its power:

1. **Transitivity:** `S ⊑ T` and `T ⊑ U` ⇒ `S ⊑ U`. So we may refine in many small steps.
2. **Monotonicity:** refining a *part* of a program refines the whole. That is what lets us split
   a spec into two sub-specs and refine each separately — the heart of the recursion in
   `agent/refiner.py`.

A chain `Spec ⊑ S1 ⊑ S2 ⊑ … ⊑ Program` ends with real code, and by transitivity the code meets the
original spec. **Each `⊑` step is justified by a law whose side-condition (the proof obligation)
is checked by Z3.**

### 1.4 What is a "proof obligation", concretely?

A law says *"Spec A is refined by this construct **provided** `<logical statement>`"*. That statement is the
obligation, usually an implication `X ⇒ Y`. To check `X ⇒ Y` with a solver we ask: *is there any
assignment of values making X true and Y false?* — if not, it's valid
(`verification/z3_backend.py:58`, `solver.add(Not(goal))`). Implication reads: "whenever X is true, Y is true."

> **Tiny implication cheat-sheet.** `x>5 ⇒ x>0` is valid. `x>0 ⇒ x>5` is not (counterexample `x=1`).
> Stronger statement = fewer states satisfy it. `x>5` is *stronger* than `x>0`.

### 1.5 The mixed language (L_mix)

During refinement a program is part-code, part-spec, e.g. `x := 0 ; w:[P,Q]`. The repo's types are
`MixNode = ProgramNode | Spec` (`lpl/ast.py:9`); `RefinementGraph.reconstruct_mixed_program`
(`graph.py:137`) returns this in-progress form; `reconstruct_program` (`graph.py:143`) insists every
hole has been filled.

### 1.6 How laws plug into code

Every law is a class with `apply(spec, parameters) → RefinementResult` (`laws/base.py`).

* **Terminal** laws return a `program` (assignment, skip, initialized_skip) — the branch ends.
* **Recursive** laws return `sub_specs` + `roles` (and maybe `obligations`) — new jobs for the LLM.
* `PARAMS` declares what the LLM must supply, as `(name, kind, default)`, where kind `"expr"` is
  parsed as an L_spec expression and `"name"` stays a bare identifier.
* `build_program(parameters, children)` says how to put the refined children back together.

---

## Part 2 — The ten laws

For each law: **Rule · Intuition · Code · Example · What the LLM must supply · Pitfalls**.
Notation: `P` precondition, `Q` postcondition, `⇒` implies, `Q[x:=E]` = Q with E substituted for x.

### Law 1 — `skip`  (terminal)

**Rule.** `w:[P,Q] ⊑ skip`  provided  **`P ⇒ Q`**.

**Intuition.** If the postcondition is *already true* when you start, there is nothing to do.

**Code.** `laws/skip.py:8`. One obligation, `assumptions=[P]`, `goal=Q` (lines 17-22), returns program `Skip()`.
Python output: `pass` (`to_python.py:48`).

**Example.** Case `A1-skip`: `P: x>5`, `Q: x>0`. Obligation `x>5 ⇒ x>0` ✓.

**LLM supplies.** Nothing (`PARAMS = ()`).

**Pitfall.** Cheap and tempting: a model may say `skip` when `P ⇏ Q`; Z3 rejects with a counterexample.
In the old results one config proposed `skip` 256 times and had 34 accepted (§Part 3).

### Law 2 — `assignment`  (terminal)

**Rule.** `x:[P,Q] ⊑ x := E`  provided  **`P ⇒ Q[x := E]`**.

**Intuition.** After `x := E`, the new x *is* E. So Q about the new x is Q with E in x's place; that
must be guaranteed by what held before (P). *Think: "pretend to do the assignment on paper by
substituting, then check what's left."*

**Code.** `laws/assignment.py:10`. Steps: read `variable`, `expr`; **`check_assignable(spec, variable)`**
(line 26) — raises `FrameViolation` if `variable` is not in the frame; compute `substitute(Q, variable, expr)`
(line 29); one obligation `P ⇒ Q[x:=E]` (lines 32-37). Output `Assignment(variable, expr)`.
`substitute` is capture-avoiding (`lspec/substitution.py:79`).

**Example (A2-assign).** `Frame: x`, `P: N≥0`, `Q: x = N+1`. Take `x := N+1`.
`Q[x:=N+1]` is `N+1 = N+1`, trivially true ⇒ obligation valid ✓.
**Example with a precondition used (A3).** `P: A>B`, `Q: m=A ∧ m>B`, take `m := A`.
`Q[m:=A]` = `A=A ∧ A>B`; needs `P` to get `A>B` ✓.

**LLM supplies.** `variable` (a name in the frame) and `expr`.

**Pitfalls.** (1) Assigning to a non-frame variable (e.g. `N`) → `FrameViolation` — the prompt now
says "You may ONLY assign to: …" because gpt-oss-120b wasted calls on this (`prompts.py:92-130`,
`frame.py` docstring). (2) Models try `x := sqrt(N)`; L_spec has no `sqrt`, so `C2-sqrt-tight` has "no closed-form assignment".

### Law 3 — `sequential`  (recursive)

**Rule.** `w:[P,Q] ⊑ w:[P,R] ; w:[R,Q]`  for **any** midpoint formula `R`. *(No obligation.)*

**Intuition.** Split a job in two with a checkpoint: first reach state `R`, then go from `R` to `Q`.
Any `R` is *legal*; a *bad* `R` just makes one of the halves impossible, and Z3 will find that out
below, when it tries to refine that half.

**Code.** `laws/sequential.py:8`. Parameter `intermediate`; `rigid_context(spec, intermediate)` (line 26)
adds the precondition's rigid facts to `R`; creates `spec1=[P,R]` and `spec2=[R,Q]` via `derive`
(inherit frame); `roles=["part1","part2"]` (line 50); `build_program` → `SequentialComposition`
(line 54). **No `ProofObligation`s** — nothing to check at this step.

**Example (B1).** `P: true`, `Q: s=A+B ∧ d=A−B`, frame `s,d`. Midpoint `R: s=A+B`.
Halves: `[true, s=A+B]` (refined by `s := A+B`) and `[s=A+B, s=A+B ∧ d=A−B]` (refined by `d := A−B`:
obligation `s=A+B ⇒ (s=A+B ∧ A−B=A−B)` ✓).

**LLM supplies.** `intermediate` — *the hard part*: it must be a formula that the first half can
establish **and** that, together with the facts carried over, lets the second half finish. From the
docs in the repo: the intermediate was "the one move no model in Study 3 found" (docstring of
`laws/iteration.py:28-50`).

**Pitfalls.** Because there's no obligation, a *useless* midpoint (e.g. `true`) is accepted
instantly and just pushes the difficulty down. `R = P` or `R = Q` produces a sub-spec identical to
the parent; the **progress guard** (`agent/refiner.py`, tests `test_progress_guard.py`) rejects that.
Another subtle trap: the second half is specified from `R` *alone*, so facts about rigid inputs (`d>0`)
are lost unless carried — hence `rigid_context`.

### Law 4 — `flexible_sequential`  (recursive, extended)

**Rule.** `w:[P,Q] ⊑ w:[A,B] ; w:[C,D]` provided
 **(1) `P ⇒ A`**, **(2) `B ⇒ C`**, **(3) `D ⇒ Q`**.

**Intuition.** Like `sequential`, but the two halves don't have to meet at one formula. The first half
may assume less than P gives (A), the second half may produce more than Q needs (D), and the "handshake"
only requires what the first half ensures (B) to be enough for what the second half assumes (C).

**Code.** `laws/flexible_sequential.py:8`. `PARAMS = pre1, post1, pre2, post2` (line 20).
Three `ProofObligation`s (lines 33-51); sub-specs `[A,B]` and `[C,D]`. Note it does **not** pass a
`description` to its obligations (unlike skip/assignment), so counterexamples are less explanatory.

**Paper vs code (important).** The docstring (lines 15-18) says the paper's Lemma 6.2 states the third
premise as `Q ⇒ D`, but its proof needs **`D ⇒ Q`** (strengthening a postcondition). The repo follows the sound direction.

**LLM supplies.** Four formulas; models almost never choose it (5 proposals, 0 accepted in the core-vs-extended experiment).

### Law 5 — `alternation`  (recursive)

**Rule (repo's simplified form).** `w:[P,Q] ⊑ if G then w:[P∧G,Q] else w:[P∧¬G,Q]`. *(No obligation.)*

**Intuition.** Case analysis. In the "then" branch you know G; in the "else" branch you know ¬G;
each must still establish Q.

**Code.** `laws/alternation.py:8`. Parameter `guard`; sub-specs `[P∧G,Q]` and `[P∧¬G,Q]`
(`BinaryOp(P,'/\\',G)`, `UnaryOp('~',G)`); `roles=["then","else"]` (line 46); builds `IfElse(guard, then, else)`.
The docstring (lines 9-16) says Morgan's general alternation (Lemma 2.6) needs the obligation `P ⇒ G1 ∨ … ∨ Gn`;
with one guard and its negation, that disjunction is a tautology, so none is emitted.

**Example (B2-max).** Spec: `m ≥ a ∧ m ≥ b ∧ (m=a ∨ m=b)`. Guard `a ≥ b`:
then-branch `[a≥b, …]` refined by `m := a`; else-branch `[¬(a≥b), …]` by `m := b`.

**LLM supplies.** A single `guard`. Note: the guard must be a boolean L_spec expression — a *bad*
guard is not rejected here; it makes a branch unsatisfiable and fails later (e.g. a branch `[P∧G, Q]` with
no valid assignment).

**Pitfall.** Nothing stops using alternation repeatedly, each time with a new guard, descending forever
without ever proving anything — which is why the refiner imposes `max_depth=6` (`refiner.py:17-30`).

### Law 6 — `iteration`  (recursive)  — the loop law, in its *simple* form

**Rule (what the code does).**
`w:[P,Q] ⊑ while G do w:[P∧G∧(V=V0) , P∧(0≤V)∧(V<V0)]`  provided  **`P ∧ ¬G ⇒ Q`**.

Here **P doubles as the loop invariant** (`laws/iteration.py:66`: `invariant_expr = spec.precondition.expr`).

**Intuition.** A loop needs three ingredients:
* **Guard G** — keep going while G is true.
* **Invariant I** — a fact true before the loop and *re-established by every iteration*. On exit,
  `I ∧ ¬G` is all you know, and it must imply Q (the obligation).
* **Variant V** — an integer-like quantity that is `≥ 0` and **strictly decreases** each iteration. A
  non-negative quantity that keeps strictly decreasing cannot do so forever ⇒ **the loop terminates**.
  Without a variant you've only proved *partial* correctness ("if it stops, it's right").

The body sub-spec says: *starting from invariant ∧ guard, with V's starting value remembered as V0
(that is the `V = V0` conjunct; `V0` is `to_previous_state(V)`, i.e. every var `x` → `x0`,
`iteration.py:11-26`), end with the invariant restored and V smaller (and still ≥ 0 in "strict" mode).*

**Code.** `iteration.py:28`; `PARAMS = guard, variant` (line 51 — **no defaults**: a missing
variant is an explicit error rather than silently `0`, lines 54-63). One obligation `P ∧ ¬G ⇒ Q`
(lines 68-74). Strict mode adds `0 ≤ V` (line 89, env `FORMALLLM_STRICT_VARIANT`, default on;
set to `0` to drop the lower bound: an ablation from commit `32bf870`). Single role `body` (line 109);
program `While(guard, body)`.

> ⚠ The class docstring (lines 28–50) talks about an LLM-supplied invariant; the code does not. That
> belongs to `initialised_iteration`. Trust the code (also noted in `07_Codebase_Tour.md`).

**Example (C4).** `P: i ≤ N`, `Q: i = N`, frame `i`. Guard `i < N`, variant `N − i`.
* Exit obligation: `i ≤ N ∧ ¬(i<N) ⇒ i = N` ✓ (integers).
* Body spec: `[i≤N ∧ i<N ∧ N−i = N0−i0 ,  i≤N ∧ 0 ≤ N−i ∧ N−i < N0−i0]`. Refine with `i := i+1`:
  `Q[i:=i+1]` = `i+1≤N ∧ 0≤N−i−1 ∧ N−i−1 < N0−i0`. From `i<N` and `N−i=N0−i0` all three hold ✓.
Python: `while (i < N): i = (i + 1)`.

**LLM supplies.** `guard`, `variant`. The *invariant is fixed to be P*, so this only works when the
precondition is already a usable invariant (C4). In C3 the precondition says `i = 0`, which no loop body can preserve
— the old benchmark note on C3 describes exactly this limitation (`cases.py` note at C3; now fixed by the next law).

### Law 7 — `initialised_iteration`  (recursive, the workhorse)

**Rule.** `w:[P,Q] ⊑ w:[P,I] ; while G do w:[I∧G∧(V=V0) , I∧(0≤V)∧(V<V0)]`
provided **`I ∧ ¬G ⇒ Q`**.

**Intuition.** Same loop, but now the LLM chooses the invariant `I` itself, and a first sub-spec
`[P, I]` ("initialise") makes `I` true before the loop starts. This is the realistic loop law:
usually the precondition is *not* the right invariant (e.g. `P: i=0`).

**Code.** `laws/initialised_iteration.py:11`. `PARAMS = guard, variant, invariant` (all required, line 20).
`invariant_expr = rigid_context(spec, invariant)` (line 35) prepends rigid precondition facts. One
obligation `I ∧ ¬G ⇒ Q` (lines 38-43). Sub-specs: `init=[P, I]` and `body` (lines 67-75).
`roles=["init","body"]` (line 80). Program: `SequentialComposition(init, While(guard, body))` (line 85).

**Example (C3, counting loop).** `P: N≥0 ∧ i=0`, `Q: i ≥ N`, frame `i:int`.
`I = (i ≤ N)`, `G = (i < N)`, `V = N − i`. Exit: `i≤N ∧ i≥N ⇒ i≥N` ✓. Init `[P, I]`: `skip`
(`N≥0 ∧ i=0 ⇒ i≤N` ✓, this is the regression test `test_engine_reachability.py:70`). Body: `i := i+1`.

**Example (the paper's sqrt, C5)** — walked through step by step in `01_Project_Big_Picture.md §4`.
Parameters: `I = x*x ≤ N ∧ x ≥ 0`, `G = N ≥ (x+e)*(x+e)`, `V = N − x*x`; init `x := 0`, body `x := x+e`.

**Example (D1 integer division).** `I = q*d + r = n ∧ r ≥ 0`, `G = r ≥ d`, `V = r`; init is itself a
`sequential` (`q := 0 ; r := n`) and the body a `sequential` with intermediate
`(q+1)*d + r = n ∧ r ≥ 0 ∧ r < r0` (`test_engine_reachability.py:94-120`) — see how much cleverness the model must supply.

**LLM supplies.** **Three** creative expressions at once: guard, variant, invariant. This is the single
biggest ask in the whole system, and it is exactly what the experiments show models failing at (Part 3).

**Pitfalls.** Wrong variant (a constant) can never decrease ⇒ body unprovable. A guard that doesn't
imply progress ⇒ same. Invariant too weak ⇒ the **exit** obligation fails (`I∧¬G ⇒ Q` needs I strong enough);
invariant too strong ⇒ the **init** or **body** fails. Z3 can return `UNKNOWN` on the nonlinear
`x*x` terms. Missing rigid facts (`e>0`) in the body were a real bug, solved by `rigid_context`.

### Law 8 — `strengthen_post`  (recursive)

**Rule.** `w:[P,Q] ⊑ w:[P,R]`  provided  **`R ⇒ Q`**.

**Intuition.** If you promise something *stronger* (R) you automatically meet the weaker promise (Q).
Useful when a stronger postcondition is easier to *reach* directly (e.g. a more specific equation).

**Code.** `laws/strengthen_post.py:9`. Parameter `intermediate_post`. Obligation
`assumptions=[R]`, `goal=Q` (lines 22-27). Sub-spec `[P,R]`, role `sub`; `build_program` returns the child's program unchanged (line 46).
*Note*: Morgan's rule may use `P` as an extra assumption (`P ∧ R ⇒ Q`); the repo conservatively uses only `R ⇒ Q`, which is sound but
slightly less permissive.

**Example.** `P: x≥0`, `Q: y>0`. Take `R: y=1` (`y=1 ⇒ y>0` ✓). Then refine `[x≥0, y=1]` with `y := 1`.

**LLM supplies.** `intermediate_post`.

**Pitfall — the identity trap.** `R = Q` discharges `R ⇒ Q` trivially and produces the *same* spec ⇒ infinite descent.
Handled by the progress guard (`test_progress_guard.py:32`). Experiment: with the extended law set, `llama3.1`
proposed `strengthen_post` 165 times (38.9% of all its proposals) and only 2 were accepted.

### Law 9 — `weaken_pre`  (recursive)

**Rule.** `w:[P,Q] ⊑ w:[R,Q]`  provided  **`P ⇒ R`**.

**Intuition (the confusing one).** If the new precondition `R` is *weaker* (true in more states), then
whoever solves `[R,Q]` must work in *more* situations — a harder job — and therefore certainly works in the
original smaller set of situations `P`. *Weakening the precondition makes the spec stronger as a promise.*

**Code.** `laws/weaken_pre.py:9`. Parameter `intermediate_pre`. Obligation `P ⇒ R` (lines 22-27); sub-spec `[R,Q]`, role `sub`.

**Example.** `P: x>5`, `R: x>0` (`x>5 ⇒ x>0` ✓). Refine `[x>0, Q]`.

**LLM supplies.** `intermediate_pre`. Same identity trap (`R = P`). Weak usefulness for LLMs: 12 proposals by `qwen3.5-nothink`, 0 accepted.

### Law 10 — `initialized_skip`  (terminal)

**Rule.** `w:[P,Q] ⊑ skip` provided **`P ∧ (x = x0 for each non-constant output var x) ⇒ Q`**.

**Intuition.** `skip` leaves every variable unchanged, so after it, each variable `x` equals its starting
value `x0`. Plain `skip` ignores that; `initialized_skip` lets the proof use `x = x0`. This matters when the
postcondition mentions `x0` (e.g. "x is unchanged").

**Code.** `laws/initialized_skip.py:8`. For each postcondition param whose name is **not all upper case**
(line 20: `if not p.name.isupper()` — a naming-convention heuristic for "constants are upper-case, variables aren't";
fragile if a spec uses different names!) it adds the assumption `x = x0` (lines 22-27). One obligation; program `Skip()`.
Its obligation description string is copy-pasted from plain skip.

**LLM supplies.** Nothing. Never proposed in the recorded experiments.

---

### Law summary table

| Law | Kind | Obligation(s) | Sub-specs (roles) | LLM parameters |
|---|---|---|---|---|
| `skip` | terminal | `P ⇒ Q` | — | none |
| `initialized_skip` | terminal | `P ∧ x=x0… ⇒ Q` | — | none |
| `assignment` | terminal | `P ⇒ Q[x:=E]` | — | `variable`, `expr` |
| `sequential` | recursive | none | `[P,R]`, `[R,Q]` (`part1`,`part2`) | `intermediate` |
| `flexible_sequential` | recursive | `P⇒A`, `B⇒C`, `D⇒Q` | `[A,B]`, `[C,D]` | `pre1 post1 pre2 post2` |
| `alternation` | recursive | none | `[P∧G,Q]`, `[P∧¬G,Q]` (`then`,`else`) | `guard` |
| `iteration` | recursive | `P∧¬G ⇒ Q` | body (`body`) | `guard`, `variant` |
| `initialised_iteration` | recursive | `I∧¬G ⇒ Q` | `[P,I]`, body (`init`,`body`) | `guard`, `variant`, `invariant` |
| `strengthen_post` | recursive | `R ⇒ Q` | `[P,R]` (`sub`) | `intermediate_post` |
| `weaken_pre` | recursive | `P ⇒ R` | `[R,Q]` (`sub`) | `intermediate_pre` |

**Pattern worth internalising:** laws whose obligations are *immediate* (skip, assignment) are
checked and *finished*; laws with *no* obligation (sequential, alternation) accept anything and
postpone the risk to the children; loop laws put the risk in **the three formulas** the LLM
writes. That is why the *kind of parameter* a law needs predicts how often models succeed with it.

---

## Part 3 — What the experiments show (law selection vs parameter synthesis)

> **Read this section skeptically.** The numbers come from files in `benchmarks/results/`; I report what
> is in them and flag what I cannot determine. Sample sizes are tiny (2–3 repeats per cell), several
> result files mix multiple invocations, and some records are infrastructure failures, not model
> failures.

### 3.0 Dating the data (so you don't mix eras)

* `results/tables.md`, `lawcmp_tables.md`, `baseline_tables.md` were last committed **2026-09-16** — *before*
  frame wiring (09-17), `initialised_iteration` (09-18, "Milestone 2") and the removal of the "oracle" arm (09-17,
  commit `ec10d7a`). They describe an **older engine**: e.g. C3 failed "because the engine reuses the precondition
  as invariant", which `initialised_iteration` later fixed (and is regression-tested now).
* `results_study.jsonl`, `results_strict.jsonl`, `results_lenient.jsonl`, `results_strict_refinement_gpt120b.jsonl`
  are the newer "Study 3" runs, all on `C5-sqrt-paper`, `repeat 0`. `results_d1.jsonl` has one run of `D1-intdiv`.
* The "oracle" rows in `tables.md` replayed a hand-written playbook and were withdrawn as misleading
  (`benchmark.py:47-51`). **Ignore the oracle row.**
* `run_log_<model>.txt` are raw UTF-16 prompt/response dumps. I did **not** derive numbers from them.

### 3.1 Earlier benchmark (older engine; 11 cases × 3 repeats; budget 30 LLM calls; T=0.2) — `results/tables.md`

Solved / attempts, "solvable" cases only (`A4-impossible` and others marked "none found" are controls):

| Config | solved (solvable cases) | notes from the file |
|---|---|---|
| llama3.1 | 17/27 (63%) | 9% malformed output; 86 Z3 rejections |
| llama3.1-wide | 11/18 (61%) | larger budget |
| qwen3.5-nothink | 11/27 (41%) | |
| qwen3.5-think | 6/27 (22%) | **81% malformed output** (99/122): `Unknown law generated by LLM: None` ×69 |
| ornith | 8/27 (30%) | 12% malformed |
| ornith-think | 9/27 (33%) | |

Per case: **tier A (skip/assign) mostly solved** by all. **Tier B (sequential / alternation: B1, B2, B3) were 0/3 for
every config.** C-tier sqrt/loop cases varied: `C1-sqrt-loose` solved only by the llama configs (3/3 and 2/2);
`C4-loop-invariant` solved by llama (3/3), qwen3.5-nothink (2/3), qwen3.5-think (3/3).

**Law selection ("proposed → accepted by Z3" per law, same file).** Examples:
`qwen3.5-nothink` iteration `116 → 115`, `ornith` skip `256 → 34`, `llama3.1` iteration `3 → 0`.
Reading it: *Z3 accepting an `iteration` step* only means the exit obligation held — the loop body is a
**child** that can still fail. A high `proposed→accepted` ratio at one level is therefore **not** end-to-end success.
Also `unknown`-law proposals (unparseable) were a large share (e.g. 165 for `ornith`).

**Failure taxonomy.** Dominant parse error: `Unexpected token Token('LPAR', '(')` — the model wrote
a call/paren form the L_spec grammar doesn't allow (e.g. `sqrt(N)`, `abs(…)`). JSON errors
(`Unterminated string`, `Invalid control character`) in the "think" models.

### 3.2 Direct generation baseline — `results/baseline_tables.md`

Same specs, but the model just writes Python (no calculus, no Z3):

| Config | Baseline solved (of 10) | Refinement pipeline (from 3.1) | Baseline time |
|---|---|---|---|
| llama3.1 | **10/10** | 63% (17/27) | 33 s |
| qwen3.5-nothink | **10/10** | 41% | 46 s |
| qwen3.5-think | 8/10 | 22% | 997 s |
| ornith | **10/10** | 30% | 80 s |
| ornith-think | **10/10** | 33% | 84 s |

**Honest reading.** On *test-based* correctness for these textbook-sized specs, plain code generation
beats the refinement pipeline by a wide margin. The refinement pipeline's value is not a higher pass
rate here; it is that **a produced program carries a proof**, whereas "PASS" in the baseline means "passed the
test inputs". (Also: "baseline solved" is judged by executing the function and checking the postcondition — not by proof.)
The newer Study 3 asks the sharper question on one hard case (below).

### 3.3 Core 5 laws vs extended 9 laws — `results/lawcmp_tables.md` (2 configs only)

| Config | Core (5 laws) | Extended (9 laws) |
|---|---|---|
| llama3.1 | 9/22 (41%) | **2/22 (9%)** |
| qwen3.5-nothink | 6/22 (27%) | **3/22 (14%)** |

More laws made things *worse*: the models reached for the new laws (`strengthen_post` = 38.9% of llama3.1's
proposals, 165 proposed → 2 accepted; `weaken_pre` = 14.5% of qwen's, 12 → 0) and wandered. Malformed output rose
(llama 3% → 11%; qwen 8% → 60%). **Takeaway: a larger menu is not free for a weak model.** (Caveat: pre-dates the
progress guard, which now blocks identity steps; I don't have a rerun to quantify the change.)

### 3.4 Study 3 on the paper's example (C5-sqrt-paper) — newer engine; `evaluate_models.py`

`evaluate_models.py` runs two arms on the same spec: **direct** (model writes Python) vs **refinement**
(model picks laws/parameters; Python emitted from the verified tree). I aggregated `all_passed` per
arm from the JSONL (these are *records*, not independent trials: files accumulate multiple invocations and
some failed for infrastructure reasons — `results_study.jsonl` has 72 records, 9 with a `transport_error`):

| File | refinement arm: models with a verified program | direct arm |
|---|---|---|
| `results_study.jsonl` | **only `gpt-oss-120b`**: 3 SUCCESS, 12 EXHAUSTED, 1 harness error (of 16 records). All 7 other configs: 0 | gpt-oss-120b 10/19 pass; llama3.1 0/9; qwen3.5-nothink 2/6; ornith 1/2; others 0 |
| `results_strict.jsonl` (variant requires `0≤V`) | gpt-oss-120b 1 SUCCESS / 1 EXHAUSTED; every other model 0 | ornith 2/2, ornith-think 2/2, gpt-oss 2/2, qwen3.5-nothink 1/2, qwen3-coder-next 1/2, llama3.1 0/2, qwen3.5-think 0/2 |
| `results_lenient.jsonl` (drops `0≤V`) | gpt-oss-120b 1 SUCCESS / 1 EXHAUSTED; every other model 0 | gpt-oss 2/2, ornith-think 2/2, qwen3-coder-next 1/2, others 0/2 |

In the successful gpt-oss-120b record (`results_study.jsonl`, first refinement record) the accepted laws were
`strengthen_post ×2, initialised_iteration ×1, assignment ×2` over 6 LLM calls — the right *shape*: pick the loop law,
supply invariant/guard/variant, finish with assignments. I did **not** verify whether the strict/lenient ablation
changes the success rate — the sample (one repeat) is far too small to say.

### 3.5 What this adds up to (the "law selection vs parameter synthesis" story, issue #3)

GitHub issue #3 ("Parameter Synthesis Assistance for LLMs") states the working hypothesis, consistent with the
tables above: *larger models (>100B) manage law selection but fail at parameter synthesis — writing the
precise formulas (invariants, intermediates) that make Z3's obligations hold.* The evidence in the repo:

* models pick a *plausible law* quickly (e.g. iteration proposals accepted at the top level),
* the **children** then fail because the invariant/intermediate was wrong or too weak (Z3 counterexamples, `UNKNOWN` on nonlinear terms),
* formatting problems (parse errors, JSON mangling, operator syntax) are a separate, large cause of lost calls for small/"thinking" models,
* only one model (`gpt-oss-120b`, ~120B) completed the paper's sqrt example via refinement, and even it exhausted its budget in most records.

What I **cannot** state from the files: a clean parameter-vs-law failure *rate* (the harness records per-attempt
status and rejection messages, but I did not tabulate them by cause), and anything about run-to-run variance (one repeat).
Proposed direction in the issue: few-shot/RAG prompting, or Milestone 6 (learned law templates that move the "mathematical lifting"
into the engine).

---

## Part 4 — Common confusions (collected)

1. **"Refining = making the spec weaker."** No: refining preserves guarantees while adding concreteness. `strengthen_post` makes the *postcondition* stronger (a bigger promise) and `weaken_pre` makes the *precondition* weaker (more situations handled) — both make the *spec* harder to satisfy, which is exactly why solving them solves the original.
2. **Invariant vs precondition.** The invariant must hold *before the loop (after init), after every iteration*, and combine with `¬guard` to give Q. It's not necessarily P.
3. **Variant vs invariant.** Invariant = "what stays true"; variant = "what shrinks" (gives termination).
4. **`x0`/`V0`.** The pre-state twin. It exists only to talk about "before vs after" inside one postcondition.
5. **No obligation ≠ no risk.** `sequential` and `alternation` emit nothing; their risk is deferred to the sub-specs.
6. **Z3 `PROVED` ≠ test passed.** Proof is for all inputs in the logic's arithmetic; tests are samples in Python arithmetic.
7. **Frame vs `Const`.** The frame says what *may* change; params (`(N:float)`) are logical constants. A variable that is neither in the frame nor a parameter is a modelling error waiting to happen.
8. **`UNKNOWN` ≠ `FAILED`.** `FAILED` has a counterexample; `UNKNOWN` is "solver couldn't decide" (often nonlinear arithmetic or timeout) — recorded as `INCONCLUSIVE`.

---

## Part 5 — Check yourself

1. State the obligation of `skip` in words, and give one spec where `skip` is correct and one where it isn't.
2. Compute, by hand, `Q[x := x+1]` for `Q ≡ x*x ≤ 9`. *(Answer: `(x+1)*(x+1) ≤ 9`.)*
3. Why does `sequential` emit no proof obligation, yet is not "free"? What is the earliest point a bad `intermediate` is caught?
4. Fill in the loop law for `P: i=0 ∧ N≥0`, `Q: i=N` with frame `i`: choose `I`, `G`, `V`; check the exit obligation by hand. *(One answer: `I: i≤N`, `G: i<N`, `V: N−i`; exit: `i≤N ∧ i≥N ⇒ i=N` ✓.)*
5. What does the variant `V` prove, and what extra obligation would show it can't go below 0? (Hint: strict mode adds `0 ≤ V` to the body's postcondition, `initialised_iteration.py:55-65`.)
6. Why can `strengthen_post` with `R = Q` loop forever, and what in the code stops it?
7. In `flexible_sequential`, which premise did the repo flip relative to the paper, and why is that direction sound?
8. Look at the table in 3.3. Give two possible reasons why *adding* laws reduced the success rate.
9. Why is "baseline solved 10/10 vs refinement 63%" not a refutation of the approach? What *does* the refinement arm give you that the baseline cannot?
10. Open `FormalLLM/tests/test_engine_reachability.py:94-120` and trace the D1 integer division: which formula is the hardest for an LLM to invent, and why?

---

## Part 6 — Where to go next

* Reading the paper: `Dr. Hou's Studies/Automated-Program-Refinement…pdf` (36 pages). Start with §2 (calculus), §6 (derived laws; the
  repo cites Lemmas 2.1, 2.6, 2.8, 6.2, 6.5, 6.6) and §9 (evaluation; §9.1.3 is where Coq/CoqHammer appear).
* The prover: this repo uses Z3; the paper uses Coq + CoqHammer. What those are, and what moving to Lean/Coq would
  mean, are covered in the other reading files in this folder.
* Code to read with this file open: `refinement/laws/initialised_iteration.py`, then `tests/test_engine_reachability.py`.
