# 25 — Presenting the Lean core to Dr. Hou: what to say, what to show, what to expect

> For the next meeting. Everything here is backed by a file: numbers by `22_Lean_Plan_Progress.md`, design by `23`, the specifications by `24`. Nothing in it needs a language model: **no model has been run on the Lean engine yet**, and the talk should say so first.

## The message in one sentence

*Following the decision of 6 October, the refinement method now runs with Lean as its only prover; a derivation is a Lean term, so the Lean kernel checks the whole thing; hand-written derivations certify on 36 of 36 tasks of a new 42-problem Lean library and on 24 of 25 tasks of Verina; and the engine rejected 342 of 344 deliberately broken steps (the other two were provably harmless) and never accepted a wrong program. The next step is a model that proposes the derivations.*

## Five slides

**1. The decision and what it required (1 min).** Z3 out, Lean 4 in, Verina as the benchmark, scoring per problem. It required four things that did not exist: a fast Lean (done earlier: a persistent REPL, 0.2 s per obligation), specifications written in Lean (42 now), an engine that reads Lean specifications (the new core), and a replacement for Z3's counter-examples (execution).

**2. The idea (3 min). Show: `23` §1 and §4.** A specification of "a value of type T with property P" is a type, `{ρ : T // P ρ}`; a program that inhabits it is a pair (result, proof). The four laws (`term`, `cases`, `bind`, `loop`) are the ways of building such a pair from smaller ones, so **a derivation is a Lean term and the kernel checks it**. Show the sum 1 + … + n: the JSON derivation (9 lines), the four obligations Lean proves in 0.01–0.06 s, the generated file ending in `theorem sumTo_spec_satisfied … := (sumTo_derived n h_precond).property`. Two consequences worth saying aloud: the *frame problem* of the earlier engine does not exist (a functional program cannot change a variable by accident), and *termination* is the type of the variant (a natural number cannot decrease for ever; the strict/relaxed question of doc 18 disappears).

**3. The paper's example (3 min). Show:** `python -m FormalLLM.lean oracle classic_sqrt_approx --imports full --source`. The square-root approximation (`x*x ≤ N < (x+e)*(x+e)`) over the rationals so that it can be executed on tests. One loop on a counter `k` with `x = k*e`, a variant `⌊(N+1)/e⌋₊ + 1 - k`, and one helper lemma that Lean proves first. Output: `certificate: compiles=True axioms=[propext, Classical.choice, Quot.sound] tests 7/7`. Point at `loop1` in the file: guard, invariant, variant, the next-state obligation.

**4. The evidence (3 min). One table:**

| | Result | Where |
|---|---|---|
| Specification library | 42 Lean specs; reference passes 551/551 tests; postcondition accepts 551/551 expected outputs and rejects 1,201/1,201 wrong ones | `24` §3 |
| Hand-written derivations, our library | **36 of 36 certified**; 475/475 tests | `24` §4 |
| Hand-written derivations, Verina's own tasks (other authors' specifications) | **24 of 25 certified** (19/20 basic, 5/5 advanced); 134/134 tests | `22` |
| Verina goals the engine can open | **188 of 189** (108/108 basic) | `22` item 6 |
| Wrong steps (mutation testing) | **342 of 344 rejected**; the 2 accepted are equivalent mutants; **0 accepted and failing a test** | `22` item 5 |
| Counter-example for a rejected step | 44% with `plausible` alone; **76% by running the loop** | `22` item 5, `23` §6 |

Say what the mutation row means and does not mean: it measures the *judgement of the engine*, not a model's ability; it is the evidence that "correct by construction" is not a slogan here.

**5. What is not shown, and the plan (1 min).** No model has met the engine; the hosted endpoint is still down (HTTP 403, monthly bandwidth limit), local models are available; the agent exists and is tested with a scripted model. Plan: a first small run with the protocol you give us (tries per problem, threshold), on the Verina tasks the library and the oracles already cover, scored per problem.

## Live demo (works offline; the square root loads all of Mathlib, about 90 s, the others about 20 s)

```
python -m FormalLLM.lean show   benchmarks/datasets/lean_specs/he_043_pairs_sum_to_zero
python -m FormalLLM.lean oracle he_060_sum_to_n --source
python -m FormalLLM.lean oracle classic_sqrt_approx --imports full --source
python benchmarks/lean_mutation_feedback.py --only he_003_below_zero --limit 4          # wrong steps and their counter-examples
```

To show the feedback a model would get, write a wrong step into a JSON file (copy the derivation printed by `to_tree`, change `<` to `≤` in a term) and run `python -m FormalLLM.lean check <task dir> <tree.json>`: it prints the unsolved goal and a run of the loop that ends with `<- the invariant is false after your step`.

## Questions he may ask, and honest answers

* **"Why drop Z3? What do we lose?"** Z3 is faster on some arithmetic and returns models. Measured: Lean proved 176 of the 180 distinct obligations of all earlier runs (99.7% weighted), so nothing the old runs needed is out of reach; the counter-examples are now found by running the loop (76% of rejected wrong steps, against 44% for the random tester alone, and 29% of Z3's old refutations by the tester on single steps). What is lost: Z3's ability to solve for a counter-example under equalities such as `q*d + r = n`. It could be kept as an optional screen; the code does not need it.
* **"What exactly is trusted?"** Lean's kernel and its three standard axioms. The engine checks that `#print axioms` of the specification theorem lists nothing else (not `sorryAx`, not `native_decide`'s axiom, not an axiom a step declared). The theorem's statement is generated from the task's own file, not from the model.
* **"Could the model cheat?"** With `sorry`, an axiom, or an expression that does not compute: caught by the axiom check and by compiling the program and running the tests. Tested.
* **"How is this different from Verina's own proof generation?"** Verina asks a model to write the whole proof in one go (its authors report 3.6% proof success for their best model; see `22`). Here the proof is assembled from small obligations that automation closes, and the model only chooses the structure. We measured the automation floor too: with the *correct* code given, a fixed cascade proves 37 of 189 Verina postconditions; the refinement route has to beat that on the rest.
* **"Helper lemmas: is that cheating?"** Seven of the 61 hand-written derivations use one. Each is proved by Lean before use (a false one is refused) and is a textbook fact (how a recursive definition unfolds one step; `base^k` for odd `k`; a library theorem that mergesort sorts). The paper's authors supplied such lemmas to Coq by hand.
* **"Why not reals, as in the paper?"** Reals cannot be executed, so tests cannot run on them; the rationals give the same derivation and a program that runs. The proof is the same kind (`nlinarith`).
* **"Is a state-passing loop still refinement calculus?"** It is the same laws with the state made explicit: an alternation, a sequential composition with an intermediate assertion, an iteration with invariant, guard and variant, and an implication obligation for the leaves (the strengthen-postcondition and weaken-precondition laws are folded into it). Doc 23 §3 has the table; this is a point to put to him.
* **"What does 24 of 25 hide?"** The 25 were chosen by us because they are within reach of the four laws; they say what the engine can express and prove, not what a model will find. `verina_basic_4` fails because the cascade cannot guess an existential witness.

## What to ask him

1. The protocol: how many tries per problem and which threshold (the pilot has been rescored per problem; his numbers decide the table).
2. Which part of Verina: all 189, the 146 we can score fully, or a subset by family.
3. Whether helper lemmas proposed by the model are acceptable inside a derivation (they are checked, but they enlarge what the model can do).
4. Whether the state-passing form is acceptable as the Lean version of the paper's laws, or he wants the imperative form with a frame.
5. Whether to keep Z3 as an optional screen for counter-examples.
