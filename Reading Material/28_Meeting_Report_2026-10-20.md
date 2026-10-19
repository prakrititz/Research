# 28 — Status report for the meeting (prepared 2026-10-19/20)

> Written for: you and Dr. Hou, at the next meeting. Everything below is measured on this machine unless marked "estimate". No language model has been run since the move to Lean; the one thing that blocks that is access to a model (§6).

## 1. In one paragraph

The project (Refine4LLM: an LLM chooses refinement-calculus laws, a prover checks every step) now runs on **Lean only**; Z3 is out of the loop. We have a Lean engine, **Lean specifications for all 164 HumanEval problems** (plus 5 classic algorithms), the **Verina** benchmark (189 tasks) behind the *same* interface, and **hand-written, kernel-checked derivations for 159 of 164 HumanEval problems and 177 of 189 Verina tasks**, each re-compiled in a fresh Lean process and mutation-tested. These derivations are not LLM output: they show that the engine can express and certify a solution for almost every task, and they are the ceiling a model-driven run can be compared against. What is missing is the model-driven run itself, because the hosted gpt-oss endpoint is down (§6).

## 2. What exists now

| piece | state | evidence |
|---|---|---|
| Lean engine (laws `term`, `cases`, `bind`, `loop`; a goal is a subtype, a derivation is a term, Lean's kernel checks it) | built, Z3 removed | doc 23; 36 library tasks certified at the first milestone |
| Lean specs for HumanEval | **164 / 164 problems** (+5 classics) | validated on 2,332 tests: reference passes 2,332/2,332, spec accepts 2,332/2,332 expected outputs, rejects 5,651/5,657 wrong ones (the 6 are reorderings the problem allows) |
| Verina behind the same interface (`--dataset verina|humaneval`) | done | doc 26; 165/189 Verina tasks pass all four spec checks; 9 do not compile on Lean 4.34.1, 14 have a postcondition Lean cannot run |
| Hand-written derivations | **HumanEval 159/164, classics 5/5, Verina 177/189** | all certified (compile + 3 standard axioms + tests) and re-compiled by `verify_derivations.py` in fresh processes |
| Mutation testing of the derivations | Verina 350 mutants → 96.0% rejected; HumanEval 378 → 97.1% | survivors are equivalent mutants or boundaries the spec allows; **no mutant was accepted and then failed a test** |
| Readable export | `exports/` (+ README) | per task: spec, English statement, derivation (JSON and text), finished Lean file, status |

Kinds of derivation (labelled in the export): HumanEval 87 `loop` / 69 `restate` / 3 `definitional`; Verina 65 `loop` / 112 `restate`. A `restate` derivation is either a decidable check or a **brute-force search over the specification's own enumeration** (all subsequences, all pairs) plus a lemma that the extremum is a member and a bound. They prove the task is reachable and the spec is satisfiable by a program; they do not demonstrate an efficient algorithm. This is the first thing a reviewer should be told.

## 3. What was done since the last meeting (chronological)

1. **Z3 discarded** (kept as a possible fast screen later); engine and tactic cascade moved to Lean only.
2. **Specs**: 26 new HumanEval specs written (so all 164 are covered), validated against the tests.
3. **One interface** for Verina and HumanEval: a dataset registry, one evaluator, one CLI; found and fixed a Verina harness bug (string/char inputs were written without quotes, so some reference solutions looked broken).
4. **Derivations**: first for the 26 new specs, then for the rest of HumanEval (107 problems), then for Verina (24 → 177), in batches, each batch gated by a regression run.
5. **Verification**: independent recompile, four spec checks, mutation tests, regression of the whole set after every change.
6. **Export + docs**: `exports/`, doc 27 (derivations: families, lemma toolkit, what is missing and why), docs 10/22/26 updated.

## 4. What the derivation work taught us (engine and harness)

* **Tasks without a precondition argument.** Three Verina tasks state the theorem for *every* input (no `h_precond`); the engine now supports that rather than weakening the statement.
* **Undecidable preconditions broke the test harness.** `∃ i j, …` cannot be decided, so tests "did not run" (this had made six reference solutions look broken). A tiny witness-search tactic fixes it.
* **The cascade tries every helper lemma on every obligation.** A list of eight lemmas exhausted the heartbeat budget of one obligation; auxiliary facts now live inside the lemma that needs them. Directly relevant for model-written helpers: a model that proposes many helpers can hurt itself.
* **`match` inside a step term is dangerous**: its auxiliary matcher does not unify cheaply with the lemma's own; `head?/tail` style terms do.
* **Spec quality is uneven.** Some Verina postconditions are unreachable by testing (undecidable), one is weak (`verina_basic_72` accepts a wrong output), three omit `h_precond`. Our own 164 are decidable by design (their price: they are less general than Verina's).

## 5. What is not done, honestly

* **No LLM-driven result on the Lean engine yet.** Every model number we have is from the Z3/Coq era (square root 100/100; 11 other solvable problems 220/220; HumanEval pilot 6/20 problems). They are still true but are a different system.
* **Not derived (12 Verina + 5 HumanEval)**: 9 Verina tasks do not compile on Lean 4.34.1 (listed, not patched); 2 are `Float` equalities that need the dataset's own axioms (the certificate refuses axioms); `mergeIntervals` is open (five coupled invariants; plan in doc 27 §7); HumanEval: three about `String.splitOn` (no lemma library in 4.34), one needs bisection/root bounds, one has an unsatisfiable spec for n > 14.
* **Specs are checked against tests, not proved equivalent to the English.** Verina has 3–10 tests per task (median 5), ours 11–16.
* **Hand-written ≠ discovered.** The derivations bound what is possible; they say nothing about how often a model finds them.

## 6. The gpt-oss endpoint, and what we can do about it

**Diagnosis (checked just now).** The endpoint `https://broodless-alethia-nipping.ngrok-free.dev/v1` answers HTTP 403 with **ERR_NGROK_725: "bandwidth limit for the month"**. It is the free ngrok plan's monthly transfer cap, not a model or credentials problem. The model host behind it may be perfectly healthy. (The credentials are not stored anywhere in the repository; the code reads `FORMALLLM_REMOTE_AUTH` from the environment.)

**Options, best first** (cost/time figures are rough estimates; check current prices):

| # | option | what it gives | effort | caveat |
|---|---|---|---|---|
| 1 | **Same model on a hosted API** (OpenRouter, Groq, Cerebras, Together, Fireworks, Hugging Face providers serve gpt-oss-120b over an OpenAI-compatible API) | the *same weights* as before, so earlier gpt-oss numbers stay comparable; no machine to keep alive | 10 min: set 3 variables (below) | needs a key and a few dollars; JSON-mode and `reasoning_effort` support differ per host (run `check_remote.py` first) |
| 2 | **Replace ngrok on the host with Cloudflare Tunnel (`cloudflared`) or Tailscale** | the lab's own model, no monthly cap | 30 min *on the machine that hosts the model* | needs whoever owns that machine; or wait for the ngrok cap to reset / pay for ngrok |
| 3 | **Claude through the Anthropic API** as a strong-model arm | a different, strong model; I can add a provider (≈ 40 lines) | 1 hour | not the paper's model family; fine as a second arm |
| 4 | **Run a smaller open model locally** (this Mac: M4, 16 GB; Ollama is installed, `gemma4:e4b` is already pulled) | zero cost, offline; matches the earlier "small local model" arms | minutes | gpt-oss-120b does not fit; gpt-oss-20b (≈ 13 GB) is borderline in 16 GB; expect low solve rates |
| 5 | **Rent or borrow a GPU** (university cluster, a 1×80 GB cloud GPU for ≈ $1–3/hour) and serve gpt-oss-120b with vLLM/llama.cpp | full control, full model | half a day | setup time; needs a tunnel again (option 2) |
| 6 | Work without a model for another week | engine-side work: `mergeIntervals`, spec strengthening, a second independent check of the specs | — | does not answer the research question |

**What I changed so that option 1 or 4 is a no-code switch** (committed; tested):

```
export FORMALLLM_REMOTE_URL="https://openrouter.ai/api/v1"     # or https://api.groq.com/openai/v1, ...
export FORMALLLM_REMOTE_MODEL="openai/gpt-oss-120b"            # the host's id for the model
export FORMALLLM_REMOTE_AUTH="Bearer <api key>"                # 'none' for a local server; user:password still works
python benchmarks/check_remote.py                              # one cheap call per config
python benchmarks/lean_agent_run.py run --config gpt-oss-120b-low --dataset humaneval --tasks he_060_sum_to_n --repeats 3
```

**Cost estimate (rough, to be replaced by a measurement).** Estimate: a derivation takes about 2–10 model calls of ~2–4k tokens (from the earlier Z3-era runs; to be re-measured). For 164 HumanEval problems × 3 repeats that is on the order of 10–30 M tokens — at the usual price of an open 120B model on a hosted API (cents to under a dollar per million tokens) a few dollars to tens of dollars. A first pilot (20 tasks × 3) would cost well under a dollar. **My recommendation:** do a 20-task pilot on option 1 (it keeps the model comparable), and in parallel ask who owns the ngrok host (option 2).

## 7. Questions for the meeting

1. **What claim do we want?** "The engine can certify X% of HumanEval/Verina with an LLM guiding it" needs the model run; until then the honest claim is "the specifications and the engine reach 159/164 and 177/189 by hand". Is that framing acceptable for an interim report?
2. **`restate` derivations.** 69 HumanEval and 112 Verina derivations are decidable checks or brute-force searches. Should the headline LLM metric be reported separately for `loop`-kind tasks (where the refinement calculus does real work)?
3. **Models.** Which arms matter to you: the paper's family, gpt-oss-120b (comparable with our old runs), Claude, small local models? Is a paid API acceptable, and who pays?
4. **Who hosts the model behind ngrok**, and can the tunnel be moved to Cloudflare Tunnel/Tailscale?
5. **Verina scope.** Report on 180/189 (patching the nine non-compiling tasks is possible but edits Verina's code) or on 189 with 9 marked "blocked by the Lean version"? And the two `Float` tasks: accept the dataset's axioms as trusted for those two?
6. **Comparability with Verina's own baselines.** Verina scores code, spec and proof generation separately; our system produces code and proof together from the spec. How do we compare?
7. **Specification trust.** We validate specs on tests. Do you want an independent second check (another author, or proving equivalence to the reference for a sample)?
8. **Still open from before:** can you share your HumanEval formal specifications and law library (Q2 of doc 12)? Our 164 would then be cross-checkable.
9. **Z3**: stay fully removed, or return as a fast pre-screen once a model is running?

## 8. Proposed next steps

1. Get one model reachable (§6, option 1 today, option 2 in parallel).
2. 20-task pilot on HumanEval (mixed `loop`/`restate`), 3 repeats, then Verina basic; record solve rate, calls, tokens, and *why* failures fail (the engine already returns counter-examples and unsolved goals).
3. Compare with the hand-written ceiling per task; report per kind.
4. Close `mergeIntervals`; decide the nine blocked Verina tasks and the two `Float` ones.
5. Independent spec check on a sample; extend tests for Verina tasks with < 5 tests.

## 9. Where everything is

`exports/README.md` (readable copy) · `Reading Material/27_Derivation_Plan.md` (derivations in detail) · `26_One_Interface_For_Verina_And_HumanEval.md` · `22_Lean_Plan_Progress.md` (log with every number) · `benchmarks/results/{humaneval,verina,lean_specs}/` (raw results).
