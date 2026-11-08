# 29 — The L_spec workflow on the Lean prover

*Branch `lspec`. Written for someone who knows the Lean core (docs 22–27) and wants to run or extend the model loop.*

## What this is, in one paragraph

The model refines a task from its specification to a program, one step at a time, exactly as in Refine4LLM: it only
chooses laws and writes their parameters, and **never writes a proof**. What is new is the language the model reads
and writes: **L_spec**, a Python-like surface (`len(l)`, `l[:i]`, `forall k: k < i ==> ...`, `x if c else y`) whose
meaning is Lean's. A translator turns each step into Lean, the Lean engine proves the obligations, and a refusal goes
back to the model in L_spec. Lean has the last word everywhere: the translation itself is checked by Lean (below), and
a solved task is a Lean term that compiles in a fresh process with no `sorry`.

```
spec (Lean) ──► goal in L_spec ──► model writes a step (L_spec JSON) ──► translator ──► Lean step
                       ▲                                                    │ repairs (only on rejection)
                       └──── refusal in L_spec (counter-example, trace) ◄── engine proves the obligations
```

## The step the model writes

One JSON object per reply, every expression in L_spec (`FormalLLM/dsl/steps.py`):

```json
{"law": "term",  "expr": "..."}
{"law": "cases", "cond": "..."}
{"law": "bind",  "var": "m", "type": "int", "prop": "..."}
{"law": "loop",  "state": [["i", "nat", "0"], ["acc", "int", "0"]],
                 "invariant": "...", "guard": "...", "variant": "...", "result": "..."}
```

A `"lemmas"` field (helper lemmas with Lean proofs) is **dropped** in a model run: the model never writes proofs.
It is used only with `--lemmas`, to check the hand-written derivations, some of which bring helper lemmas.

## Is the translation right? (checked by Lean, not by eye)

Every hand-written derivation is translated to L_spec and back, and Lean confirms the result means the same:

| check | HumanEval | classic | Verina | script |
|---|---|---|---|---|
| steps identical in Lean after the round trip | 381/381 | 11/11 | 323/323 | `benchmarks/lspec_steps.py` |
| whole derivations unchanged in meaning (`#lspec_same`) | 159/159 | 5/5 | 177/177 | `benchmarks/lspec_equiv.py --transform lspec` |
| task definitions unchanged in meaning | 390/390 | 10/10 | 399/399 | `benchmarks/lspec_specs.py` |

Last re-run 2026-11-08, after the method-spelling change (`l.sorted()`, `l.indexOf(x)`, `l.len()` now read as
L_spec). `--no-lean` on the first and third script runs only the text round trip (seconds, no Lean).

## Repairs: Python's distinctions that Lean makes and the model does not

Lean separates things Python does not: a character and a one-character string, a string and a list of characters, a
truth value and a number. When Lean refuses a step **only** for such a reason, the translator inserts the conversion,
checks the step again, and tells the model what it changed (`FormalLLM/dsl/repair.py`). A step Lean accepts is never
touched. The rules:

* a value where a `bind` needs a statement: `m = (value)`;
* type mismatches: `List Char`↔`String`, `Char`→`String`, a one-character string literal→`Char`, `[]`→`""`,
  a truth value used as a number→`1 if p else 0` (all occurrences, or one at a time);
* a conversion to the type the value already has (`toNat` of a Nat, `list(...)` of a list): dropped;
* arithmetic on a truth value: wrapped as a number;
* `}` typed for `)`, when the text has no `{` at all and the counts match (a typo with one reading).

Measured on the saved replies of qwen3.5 (probe v6, 198 steps), with no new model calls (`--model replay:<file>`):
accepted 151 → **159**, at the first attempt 102 → **140**, and **0** steps lost. Of the 39 still refused, 10 replies
were cut off mid-JSON (the model is now told so, instead of "no JSON object found"), and most others are real
mistakes (the loop's `result` used inside its invariant, unknown functions) that no rule should guess at.
`--no-repair` turns all of this off for the ablation.

## The loop (`FormalLLM/lean/lspec_agent.py`)

`LSpecAgent(provider, workflow)` mirrors the Lean agent (`agent.py`):

* **joint**: one call chooses the law and writes it; **split**: a selector call names the law, an applier call
  writes it; an unproved step, or a goal failing twice, goes back to the selector;
* a goal out of attempts (`--attempts`) withdraws the step that created it and its parent is tried again
  (`--retractions`);
* `--samples n`: up to n replies per attempt, the first the prover accepts is kept (best of n);
* `--max-binds k`: a goal already under k `bind` steps may not take another (a chain of binds only postpones the goal);
* `--examples k`: k worked examples in each prompt, retrieved by TF-IDF from the 715 hand-written steps
  (`exports/lspec_examples.json`, built by `benchmarks/lspec_examples.py`). By default (`--pool cross`) a task only
  sees the **other** benchmark's steps (HumanEval sees Verina and vice versa), so no near copy of its answer is shown.

### What the model is told when a step is refused

* *unreadable*: which field could not be read, or Lean's type error with the statement in L_spec;
* *false*: a counter-example. For a loop body, the loop is **run** on inputs `plausible` found
  (`FormalLLM/lean/dynamic.py`), and the trace shows each state, where the invariant breaks, **which top-level part
  of the invariant is false** (in L_spec), and for a wrong initial value, the initial state;
* *unproved*: the obligation in L_spec (it may be true; the prover could not show it).

### When is a task solved?

When the derivation is complete **and** its Lean file compiles in a fresh `lake env lean` process
(`benchmarks/verify_derivations.py`): no error, only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), the dataset's own precondition and postcondition (text compared with `task.lean`), and every test
`true`. The REPL's own certificate is also recorded, but it can time out on a long session (he_001: over 300 s in the
REPL after an hour of obligations, 109 s as a file). The files are kept in `benchmarks/results/lspec/verified/`.

## Running it

| want | command |
|---|---|
| the loop with the hand-written steps (no model; tests loop, translation, certificate) | `python benchmarks/lspec_run.py --dataset humaneval --model gold --limit 20 --attempts 1 --retractions 0` |
| the same, helper lemmas allowed | add `--lemmas` |
| a model end to end | `python benchmarks/lspec_run.py --dataset humaneval --model remote:gpt-oss-120b --workflow split --examples 2` |
| one step at a time at every gold goal | `python benchmarks/lspec_applier.py --dataset humaneval --model remote:<config> --level elaborate` |
| re-check saved replies after a translator change (no model) | `python benchmarks/lspec_applier.py --dataset humaneval --model replay:<results.jsonl> --level elaborate` |
| is the remote server up? | `python benchmarks/remote_check.py` |

Results go to `benchmarks/results/lspec/run_<dataset>_<model>[_switches]_<workflow>.jsonl`, one row per task and trial;
a rerun resumes. With `--model gold`, use `--attempts 1 --retractions 0`: the gold answer is the same every time, so
retrying only costs time.

### Models and money

* `remote:<config>` (e.g. `gpt-oss-120b`) goes to the server at `FORMALLLM_REMOTE_URL` (default: the ngrok address)
  with the login in `~/.formalllm/remote_auth` (`user:password`, HTTP Basic; never printed, never committed).
  A server on this machine or behind ngrok is free: no cap is asked and no cost is counted.
* Any other host (OpenAI, OpenRouter, ...) is paid: the run refuses to start without `--max-usd <cap> --paid-ok`.
* The OpenAI key (`OPENAI_API_KEY`, `~/.formalllm/openai_key`) is sent to `api.openai.com` only; before 2026-11-08 it
  was tried first for every host, so a remote server could have received it.

## Status (2026-11-08)

* Translation: verified in full (table above).
* End to end with the gold steps: he_000, he_002, he_003, he_004 solved without helper lemmas, he_001 only with its
  lemmas (all verified in a fresh process). The gold subset run (interrupted after he_004; resumable) (first 20 HumanEval tasks, strict, then `--lemmas` on the
  failures, then split on 3) measures how many tasks the prover can finish **without** helper lemmas: the most a model
  can score under the strict rule. 49 of the 159 HumanEval and 97 of the 177 Verina derivations use helper lemmas.
* Speed: was 5–60 minutes per task on the Windows PC, almost all of it re-elaborating the lemma library in every
  environment and certificate. Since 2026-11-08 the library is elaborated once per REPL and imported as a compiled
  module in the fresh-process check: he_002 went from 334 s to 50 s end to end (`HANDOFF.md` §5.1).

## Next

1. Raise the strict ceiling: turn the helper lemmas the strict gold run still needs into general library lemmas
   (`FormalLLM/lean/lemmas.py`) that the prover uses on its own.
2. A cache of proved obligations, so repeated and ablation runs do not prove the same statements again.
3. Model runs (remote gpt-oss when the server is back): joint vs split, with and without repairs, examples, samples.
