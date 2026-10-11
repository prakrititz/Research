# 23 — The Lean core: how refinement works when Lean is the only prover

> Written 2026-10-08. Code: `FormalLLM/lean/` (`session.py`, `task.py`, `laws.py`, `engine.py`), tests: `FormalLLM/tests/test_lean_core.py`, `test_lean_agent.py`, `test_lean_specs.py` (110 tests for the new core). It replaces the Z3 engine of `FormalLLM/refinement/` for the plan decided with Dr. Hou on 2026-10-06 (Lean 4 only, tested on Verina). The old engine is untouched, so every earlier result still replays.

## 1. The idea in one paragraph

A specification says *what* a function must satisfy. In Lean the specification of "a value `ρ` of type `T` with property `post ρ`" is a type, the **subtype** `{ ρ : T // post ρ }`: a value of that type is a pair of a result and a proof that the result is good. Refinement then becomes ordinary Lean programming with one rule: **a derivation is a term of the subtype**. The laws are the ways of building such a term from smaller ones; a law that cannot be justified does not type-check. When the whole term is accepted by Lean, `.val` is the program and `.property` is the proof that the program meets the specification. That is "correct by construction" in the sense of the paper, with the Lean kernel as the judge instead of Z3 or Coq.

## 2. A task, as Verina writes it

Verina's tasks (and our own, see doc 24 when written, and `benchmarks/datasets/lean_specs/`) are directories with `task.lean`:

```lean
def containsConsecutiveNumbers_precond (a : Array Int) : Prop := True
def containsConsecutiveNumbers_postcond (a : Array Int) (result : Bool) (h_precond : …_precond a) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result
```

Everything else in the file (the reference code, the proof) is *not* shown to the engine. `LeanTask` (`task.py`) keeps only the **prelude**: the helper definitions, `f_precond` and `f_postcond`. The root goal is: context `a : Array Int`, hypothesis `h_precond : f_precond a`, result type `Bool`, postcondition `f_postcond a ⟪r⟫ h_precond` where `⟪r⟫` is a hole for the result.

## 3. Goals and laws

A **goal** is (variables in scope, hypotheses, result type, postcondition with the hole). It stands for the subtype `{ ρ : T // post[ρ] }`. There are four laws; each (a) states **obligations** that Lean must accept, (b) produces **sub-goals**, (c) renders a Lean term from the terms of the sub-goals.

| Law (`laws.py`) | Paper's law | Obligations | Sub-goals | Lean term |
|---|---|---|---|---|
| `term(E)` | assignment, skip, and the strengthen-postcondition / weaken-precondition laws (the implication is the obligation) | `hyps ⊢ post[E]` | none | `⟨E, by tactics⟩` |
| `cases(c)` | alternation | `c` is decidable | `c ⊢ goal`, `¬c ⊢ goal` | `if h : c then … else …` |
| `bind(x, T, R)` | sequential composition with an intermediate assertion | `R` is a proposition | find `x : T` with `R x`; then goal with `x`, `R x` in scope | `match (… : {x : T // R x}) with ⟨x, h⟩ => …` |
| `loop(state, init, I, G, V, result)` | iteration | `I[init]`; `I ∧ ¬G ⊢ post[result]`; `G`, `V : ℕ` well-formed | body: find the next state `s'` with `I s' ∧ V s' < V s` | a recursive definition on `V` |

Two points where this differs from the paper, deliberately:

* **No frame, no assignment to variables.** Lean programs are functional: a loop has an explicit *state* (a tuple), the body returns the next state, and everything else is immutable. The frame problem that cost us a whole study (issue 1) does not exist here: a variable cannot be changed by accident because it cannot be changed.
* **Termination is the type of the variant.** The variant `V` must have type `ℕ`; the loop is defined by well-founded recursion on it (`termination_by V`), and the body's obligation `V s' < V s` is exactly the "strictly decreases" condition. The question of strict versus relaxed termination (`0 ≤ V < V0` or `V < V0`) from doc 18 disappears: a natural number cannot go below zero, and the Lean kernel rejects a definition whose decrease it cannot see.

Substitution is left to Lean. "The invariant holds for the next state" is stated as `(fun (i : Nat) (s : Nat) => INV) (ρ).1 (ρ).2`, and the tactic cascade starts with `dsimp only`, which reduces the application. The module never edits expressions textually except for the hole.

## 4. Worked example: the sum 1 + … + n

Task: `sumTo (n : Nat) : Nat`, postcondition `2 * result = n * (n + 1)`. The derivation (JSON, as written by a person or a model):

```json
{"law": "loop", "state": [["i","Nat"],["s","Nat"]], "init": ["0","0"],
 "invariant": "s * 2 = i * (i + 1) ∧ i ≤ n", "guard": "i < n", "variant": "n - i", "result": "s",
 "children": [{"law": "term", "expr": "(i + 1, s + (i + 1))"}]}
```

Obligations Lean checks for the `loop` step (all proved in 0.01–0.06 s): the guard is decidable; the variant is a `Nat`; `(fun i s => s*2 = i*(i+1) ∧ i ≤ n) 0 0`; and `s*2 = i*(i+1) ∧ i ≤ n ∧ ¬ i < n ⊢ 2 * s = n * (n+1)`. For the body (`term`): `s*2 = i*(i+1) ∧ i ≤ n ∧ i < n ⊢ ((s+(i+1))*2 = (i+1)*((i+1)+1) ∧ i+1 ≤ n) ∧ n-(i+1) < n-i`. The engine then assembles one Lean file (`Derivation.source()`):

```lean
def loop1 (n : Nat) (h_precond : sumTo_precond n) (i : Nat) (s : Nat) (h1i : s * 2 = i * (i + 1) ∧ i ≤ n)
    : { ρ : Nat // sumTo_postcond n ρ h_precond } :=
  if h1g : i < n then
    match (⟨(i + 1, s + (i + 1)), by …⟩ : { ρ : Nat × Nat // INV' ∧ V' < n - i }) with
    | ⟨(i', s'), h1b⟩ => loop1 n h_precond i' s' h1b.1
  else ⟨s, by …⟩
termination_by n - i
def sumTo_derived … : {ρ : Nat // …} := loop1 n h_precond 0 0 (by …)
def sumTo … : Nat := (sumTo_derived n h_precond).val
theorem sumTo_spec_satisfied … : sumTo_postcond n (sumTo n h_precond) h_precond := (sumTo_derived n h_precond).property
#print axioms sumTo_spec_satisfied
```

`sumTo_spec_satisfied` has the name and statement of Verina's own theorem, so the result is a complete Verina solution: code *and* proof.

## 5. How a step is judged, and how a failure is reported

1. **Each law's obligations are proved on their own** (`Derivation.apply`). The task's definitions are loaded once into a Lean environment; each obligation is a separate `theorem` checked in it (about 0.01–0.4 s). The tactic cascade is `dsimp only; split ∧; first | omega | grind | simp_all | nlinarith | aesop`, with a heartbeat limit so that the result does not depend on how fast the machine is.
2. **A failure carries what a repair needs.** The cascade is run in a *diagnosis* form where any part it cannot close becomes `sorry`; the Lean REPL then returns the goal state of each such part. Example (a wrong step `s + i` instead of `s + (i + 1)`): `not closed: n i s : ℕ, h1i : s * 2 = i * (i + 1) ∧ i ≤ n, h1g : i < n ⊢ (s + i) * 2 = (i + 1) * (i + 1 + 1)`, and `counter-example: n := 1, i := 0, s := 0` from Lean's `plausible`. An ill-formed expression is reported in Lean's own words (`unexpected token ')'; expected term`); a name already in use or a wrong number of initial values is reported before Lean is asked.
3. **The finished tree is one term** (`Derivation.source`). `certify()` compiles it (this re-checks every obligation in its real context, the second line of defence), requires that `#print axioms` of the specification theorem lists no `sorryAx`, and evaluates the program on the task's tests.

## 6. Counter-examples without Z3 (measurement)

Two sources, both Lean's own.

**`plausible`** (Lean's property tester), asked about one obligation: it works on the types of the Verina tasks (`Int`, `Nat`, `List`, `Array`, `String`, `Bool`, options) and shrinks (`l := [0, 1]`), but (1) it needs a larger instance-synthesis limit for long statements, (2) it **cannot satisfy equalities** such as `q * d + r = n` or invariants such as `acc = (l.take i).filter p` by random sampling and gives up, (3) it has no sampler for reals. On the 794 obligations Z3 had refuted in the old runs it found 29%, no better than a small-grid search (24%); on the engine's own wrong steps it found 44%.

**Running the loop** (`FormalLLM/lean/dynamic.py`): when a loop body is refused, draw only the *task's inputs* (their preconditions are usually weak), start from `init`, apply the candidate body, and check at every iteration that the invariant holds, that the variant decreases and, when the guard fails, that the postcondition holds. A correct invariant holds on every state reached from real inputs, so a violation is a real fault, and the run is a readable trace (doc 22 shows one). It raises the share of rejected wrong steps with a counter-example from 44% to 76%. The harness is generated Lean; if it does not elaborate (an undecidable invariant) there is no finding and the unsolved goal state, which accompanies every rejection, remains. The seed is fixed so that results are replayable.

## 7. Layout

| File | Role |
|---|---|
| `FormalLLM/lean/session.py` | one Lean REPL process, Mathlib imported once, a wall-clock limit on every command (kill and restart on timeout), `load()` keeps declarations |
| `FormalLLM/lean/task.py` | `LeanTask.from_dir` (Verina layout), prelude extraction, test commands |
| `FormalLLM/lean/laws.py` | `Goal`, `Obligation`, laws `Term`, `Cases`, `Bind`, `Loop`, `law_from_json` |
| `FormalLLM/lean/lemmas.py` | proved lemmas the cascade may use (list/array members versus indices, a prefix plus one element, string length) |
| `FormalLLM/lean/engine.py` | `Derivation`: `apply` (with optional helper lemmas), `apply_tree`, `retract`, `open_goals`, `source`, `certify`, `to_tree`; `make_cascade` |
| `FormalLLM/lean/dynamic.py` | counter-examples by running the loop on random inputs |
| `FormalLLM/lean/__main__.py` | `python -m FormalLLM.lean show/check/oracle/solve` |
| `FormalLLM/lean/agent.py` | `LeanAgent`: shows a goal as Lean prints it, asks a model for one law (or a nested derivation), applies it, feeds the rejection back, withdraws a step whose sub-goal cannot be solved |
| `benchmarks/datasets/lean_taskfile.py` | writes a task in Verina's directory format |
| `benchmarks/datasets/lean_specs.py` | the specification library with validators (doc 24) |
| `benchmarks/datasets/lean_oracle.py`, `verina_oracle.py` | hand-written derivations for the library and for Verina tasks, run through the engine |
| `benchmarks/lean_mutation_feedback.py` | mutation testing of the engine's judgement |
| `benchmarks/cex_plausible.py` | the Phase 3 measurement of Lean's counter-example finder |
| `benchmarks/verina_goal_check.py` | can the engine open each of Verina's 189 goals (188 can) |
| `benchmarks/lean_agent_run.py` | trial runner with per-problem scoring and replay for the agent (built, not run) |
| `benchmarks/lean_persistent.py` | the earlier prototype of the REPL wrapper, still used by the audit scripts of doc 22; `FormalLLM/lean/session.py` supersedes it |

## 8. Three things added while using it

**The tactic cascade grew from evidence, not from guessing.** The first hand-written derivations were certified 20 of 25. Each rejection was a *bridge* between two ways of writing one fact, and each became a proved lemma (`lemmas.py`) or a tactic alternative (`engine.make_cascade`); the table is in doc 24 section 4. The cascade is now: `dsimp only`; split `∧`; then the first of `omega`, `grind`, `simp_all` (alone, with the lemma set, with the lemma set then `omega`, with commutativity, after `split` or `split_ifs`), `nlinarith`, `aesop`. Two rules learned the hard way: an unconditional lemma that *unfolds* a term can fight a core `simp` lemma that *folds* it (`List.take_append_getElem`) and make `simp` loop, so the folding one is removed from the simp set; and `aesop` succeeds without closing the goal unless it is followed by `done`.

**A step can bring helper lemmas.** `{"law": "loop", …, "lemmas": [{"name": "sumTo_succ", "statement": "…", "proof": "by …"}]}`. Lean proves each lemma first (a false one is refused and nothing enters the environment); accepted ones are added to the environment, to the simp set of every later obligation, and to the finished file. This is the analogue of the lemmas the paper's authors supply to Coq by hand, with the difference that here a model may propose them and the kernel disposes. It is what a task like Verina's `arraySum` needs, whose specification is a recursion `simp` cannot unfold safely.

**A model-driven loop exists.** `LeanAgent` (tested with a scripted model, no network): the prompt holds the law cards, the task description and definitions, and the goal printed by Lean (`n : ℕ`, `h_precond : …`, `⊢ ∃ ρ, post`), plus the last three rejections for this goal; a reply may be one law or a nested derivation (the accepted prefix is kept); after `attempts_per_goal` failures on a goal the law that created it is withdrawn (`Derivation.retract`) and the parent is asked again with the failure in its history; a dead endpoint ends the trial as `NETWORK`, never as a failure of the method (the classification of `llm/transport.py` is reused).

## 9. What is not built yet

* A **model run**. Everything in doc 22's 2026-10-08 entry is model-free. The agent has not met a real model.
* Counter-examples for **nested loops** (a loop under a `bind` whose property is a hypothesis of the inner loop): 94 of 342 rejected mutants still have only the unsolved goal state. The run could replay the outer derivation to produce the bound value instead of drawing it.
* A **`fold` law** over a list, recursion on a structure, aux definitions written by the model (the helper-lemma path exists, a helper *definition* does not).
* Verina tasks with **non-trivial preconditions** in the test harness (23 tasks), and the `Array`-heavy advanced tasks (membership, `Array.any`, `eraseIdx`): the oracles show one more bridge is needed for each family.
