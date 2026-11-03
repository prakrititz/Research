# 08b — Current Issues, and How We Are Taking Them Forward

*Last updated: 2026-10-02. Everything here is checked against the actual repo; where I'm unsure I say so.*

## 0. First, a correction about "Lean/Coq"

You and I had talked about "Lean/Coq" and "making these robust". Here is what the repo actually contains:

| Claim | Reality (verified) |
|---|---|
| The code uses Coq | **No.** `grep` for coq/lean finds zero uses in `FormalLLM/*.py`. |
| The code uses Lean | **No.** Neither is mentioned. |
| The *paper* uses Coq | **Yes.** Refine4LLM is "based on Coq, CoqHammer, and GPT-4" (paper §9.1.3). Its spec language L_spec is "a subset of the language of Coq". |
| What verifies our proofs | **Z3**, an SMT solver (`FormalLLM/verification/z3_backend.py`). |
| Lean/Coq installed on this PC | **Neither.** `coqc`, `coqtop`, `lean`, `lake` are all absent from PATH. |

So "robust Lean/Coq" can mean two different projects. I have done (A) and proposed (B):

* **(A) Harden the verification layer we actually have (Z3).** This is the stand-in for Coq. Done in part — see §2.
* **(B) Add a real Coq and/or Lean backend**, so a proof obligation can be checked by a proof assistant instead of (or in addition to) Z3. Not started. Plan in §4. **This needs your decision** — see §5.

If you meant something else by "Lean/Coq", tell me and I'll re-aim.

## 1. What is wrong today (the real issue list)

### 1.1 GitHub issues
| # | State | Title | Meaning in plain words |
|---|---|---|---|
| 1 | closed | Engine is missing Frame | The engine didn't track which variables a spec may change. Fixed. |
| 2 | closed | Milestone 2: derived/composite laws | Added more refinement laws. Fixed. |
| **3** | **open** | **Parameter Synthesis Assistance for LLMs (M6)** | **The big research problem.** Big models can *choose the right law* but cannot *write the right formula* (an invariant, an intermediate assertion). Zero-shot prompting isn't enough. |

### 1.2 The core research problem (Issue #3), explained
Refinement works in two moves each step:
1. **Law selection** — "use `iteration` here". Models >100B do this well.
2. **Parameter synthesis** — "…with invariant `x*x <= N`, guard `...`, variant `...`". This is *creative mathematics*. If the formula is wrong, Z3 rejects it and the run stalls.

Ideas on the table (from the issue):
* Few-shot examples / retrieval of similar solved problems in the prompt.
* **Milestone 6**: "learned law templates" — the engine proposes candidate invariants itself (e.g. by weakening the postcondition, a classic technique) and the LLM only picks among them.

### 1.3 Robustness weaknesses I found while reading the code
| # | Weakness | Where | Status |
|---|---|---|---|
| R1 | **No solver timeout** — a hard obligation could hang an entire run. | `verification/z3_backend.py` | **Fixed** (10 s default, `FORMALLLM_Z3_TIMEOUT_MS`) |
| R2 | **Unsupported operator returned `None` silently**, producing a confusing downstream error. | `lspec/z3_translator.py` | **Fixed** (explicit error) |
| R3 | **"Inconclusive vs rejected" decided by searching the error text for the word "unknown".** Fragile. | `agent/refiner.py` | **Fixed** (typed `VerificationUnknown`) |
| R4 | Invalid escape sequence `" /\ "` in a normal string (SyntaxError in future Python). | `verification/z3_backend.py` | **Fixed** |
| R5 | Untyped names silently default to **Real**, even if the user meant integer → wrong answers like integer-division bugs. Partly mitigated by `obligation_params`. | `lspec/z3_translator.py` | Open |
| R6 | `ArraySlice` is unsupported in Z3 ("requires axioms"). | `lspec/z3_translator.py` | Open |
| R7 | Quantifiers & nonlinear arithmetic → Z3 may say `unknown`; there is no fallback prover. **This is exactly where Coq/Lean/CoqHammer would help.** | whole verification layer | Open → Plan B |
| R8 | The refiner catches `Exception` broadly and uses `locals().get('law')`; errors are recorded but hard to reason about. | `agent/refiner.py` | Open |
| R9 | Stale docstring: `IterationLaw` describes an "LLM-supplied invariant" but the code (correctly, for that law) uses the precondition; the invariant version lives in `initialised_iteration.py`. | `refinement/laws/iteration.py` | Open (cosmetic) |
| R10 | Uncommitted junk at the end of `llm/prompts.py` (blank lines and a lone `#`). | `llm/prompts.py` | Open — your uncommitted edit, I left it alone |
| R11 | `FORMALLLM_STRICT_VARIANT` is read from an environment variable inside the law itself — hidden global state that makes experiments hard to reproduce. | `laws/iteration.py` | Open |

## 2. What I changed this session (all 110 tests pass; was 105)
1. `z3_backend.py` — solver timeout; fixed the escape sequence.
2. `z3_translator.py` — unsupported operators now raise a clear error.
3. `refinement/engine.py` — new `VerificationUnknown` (a subclass of `VerificationError`, so old code still works).
4. `agent/refiner.py` — uses `isinstance(e, VerificationUnknown)` rather than string search.
5. `tests/test_z3_backend.py` — 5 new tests (proved / failed-with-counterexample / unsupported operator / timeout / error type).

Nothing is committed. Review with `git diff`.

## 3. Why these matter for *research*
If a benchmark run hangs or mislabels a timeout as a wrong answer, your results are polluted: you'd conclude "the model's invariant was wrong" when really "Z3 gave up". Separating **REJECTED** (a counterexample exists — model's fault) from **INCONCLUSIVE** (solver gave up — nobody's fault) is a *measurement-validity* fix, not just cleanup.

## 4. Plan B — a real Coq/Lean backend (proposal, not started)

```
ProofObligation (assumptions, goal)
        |
        v
  [ Backend interface ]  verify(obligation) -> PROVED | FAILED(cex) | UNKNOWN
     |         |            |
   Z3 (now)  Coq (new)   Lean (new)
```
Steps:
1. **Backend interface.** Extract `verify_obligation` behind a small protocol so backends are swappable and testable.
2. **Translator to Coq/Lean text.** Walk the same L_spec AST (`lspec/walk.py`) and print `Goal forall x, ... -> ...` (Coq) or `theorem t : ∀ x, ... → ...` (Lean). Integers → `Z`/`Int`; our reals are the hard part (Coq `R`, Lean `ℝ`; proving real arithmetic needs `lra`/`nlinarith`-style tactics).
3. **Runner.** Write a temp file, run `coqc` / `lake env lean` with a timeout, parse stdout/stderr. *Success = exit code 0 with no errors.* Failure gives an error message but **not a counterexample** — a real difference from Z3 (see §5).
4. **Automation tactic.** Coq: `lia`, `nra`, or CoqHammer's `hammer`. Lean: `omega`, `nlinarith`, `decide`. These are the "robustness" of the backend.
5. **Fallback chain.** Z3 first (fast, gives counterexamples); only if it returns UNKNOWN, escalate to Coq/Lean.
6. **Tests** that run only if the tool is installed (`pytest.mark.skipif`).

Rough effort: interface + Coq translator ≈ a few days of focused work; CoqHammer on Windows is the risky part (use WSL).

## 5. Decisions I need from you
1. **Do you want Plan B at all?** Or is "make the Z3 layer robust + solve Issue #3" the real goal?
2. If yes: **Coq or Lean first?** (Paper = Coq. Lean has the better modern tooling/community. My lean: Coq first, since it matches the paper you're reproducing and L_spec is already Coq-flavoured.)
3. May I **install** Coq/Lean (Windows installers or WSL)? I won't install anything without your OK.

## 6. Suggested next steps (in order)
1. You read `01`, `02`, `06` to get oriented (≈ 1–2 h).
2. Reply to the §5 questions.
3. I tackle R5/R8/R11, then Issue #3 (few-shot prompts + a candidate-invariant generator).
4. Re-run the benchmark and compare against the existing `run_log_*.txt`.
