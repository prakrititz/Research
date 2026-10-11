# 07 — Codebase Tour: where everything lives

> Companion to `01_Project_Big_Picture.md`. Goal: after this file you can open any file in the repo
> and know what role it plays. Line numbers are as of this writing and **will drift** (the working
> tree has uncommitted edits to `agent/refiner.py`, `refinement/engine.py`, `verification/z3_backend.py`,
> `lspec/z3_translator.py`, `llm/prompts.py` and `tests/test_z3_backend.py`).

---

## 0. Top-level layout

```
Symbolic_LLM/
├── README.md                 project description + Mermaid architecture diagram
├── main.py                   interactive demo: refine ONE hard-coded sqrt spec with an Ollama model
├── benchmark.py              refine ONE benchmark case:  python benchmark.py <model> <case_id>
├── FormalLLM/                ← the actual library (everything below)
├── benchmarks/               ← experiments: cases, harness, baselines, results, viewer
├── run_log_<model>.txt       raw prompt/response logs from model runs (UTF-16 text; see §9)
├── Dr. Hou's Studies/        reference PDFs (the Refine4LLM paper + 2 position papers)
└── Related Work/             more PDFs on neuro-symbolic AI
```

The library `FormalLLM/` is organised **by stage of the pipeline**:

```
FormalLLM/
├── lspec/         ① the SPECIFICATION language (parse, AST, substitute, → Z3)
├── lpl/           ② the tiny PROGRAMMING language + Python code generation
├── refinement/    ③ the CALCULUS: laws, engine, frame reasoning, the graph of attempts
├── verification/  ④ proof obligations + the Z3 backend
├── llm/           ⑤ talking to models: prompts, providers, response parsing
├── agent/         ⑥ the control loop (search + retries + backtracking)
├── execution/     ⑦ run generated Python in a subprocess
├── trace/         ⑧ serialise a run to JSON/text
└── tests/         pytest suite (105 passing at time of writing)
```

Data flow, left to right:

```
text spec ─► lspec.parse ─► Spec ─┐
                                  ▼
              llm.prompts ◄── agent.refiner ──► llm.provider ─► model
                                  │   ▲                │
                                  │   └─ llm.parser ◄──┘ (JSON → law + params)
                                  ▼
                       refinement.engine ─► laws ─► RefinementResult
                                  │                 (sub_specs | program, obligations)
                                  ▼
                       verification.z3_backend ◄─ lspec.z3_translator
                                  │ PROVED / FAILED / UNKNOWN
                                  ▼
                       refinement.graph (records everything)
                                  ▼ reconstruct
                       lpl.to_python ─► execution.runner ─► ExecutionResult
                                  ▼
                       trace.serializer  (JSON / text report)
```

---

## 1. `lspec/` — the specification language (L_spec)

**Purpose:** represent and manipulate logical formulas and specifications.

| File | What it is | Key things |
|---|---|---|
| `grammar.lark` | The grammar (Lark parsing library) | `spec: frame? "Precondition:" definition "Postcondition:" definition` (line 8); `frame: "Frame:" ...` (10); operators `/\ \/ ~ forall exists < <= = > >= <> + - * /`; array `a[i]`, slice `a[i:j]`; "previous state" names like `x0` (`PREV_STATE`, line 53) |
| `ast.py` | The data classes | Types (`IntType`, `FloatType`, `ArrayType`…, lines 5–31); `Param`, `Definition`, **`Spec`** (precondition, postcondition, optional `frame`, line 50); expressions `BinaryOp`, `UnaryOp`, `Variable`, `Const`, `Number`, `BooleanConst`, `VariablePreviousState`, `ArraySelect`, `ArraySlice`, `QuantifiedExpr` |
| `parser.py` | text → AST | `LSpecTransformer` (14), **`parse_spec`** (128), `resolve_names` (101: names bound by `(N:float)` become `Const`, free names stay `Variable`) |
| `substitution.py` | `Q[x := E]` | `get_free_vars` (22), `alpha_rename` (40), `substitute` (79) — capture-avoiding substitution; the assignment law relies on it |
| `walk.py` | Generic AST traversal | a *registry* of node shapes (`register`, 67; `children`, 91; `map_children`, 142) so new node types (incl. L_pl nodes, `lpl/ast.py:150-165`) are traversed with no per-function edits |
| `z3_translator.py` | AST → Z3 formulas | `Z3Translator.translate` (30); `Int/Nat → IntSort`, `Float → RealSort`, arrays are `Array(Int,Int)` (8–28) |

**Read first:** `ast.py` (113 lines, just data classes), then `grammar.lark`, then `parser.py`.

**Concept:** an expression like `x*x <= N` becomes
`BinaryOp(BinaryOp(Variable x,'*',Variable x),'<=',Const N)`. `N` is a `Const` because it appears in
the `(N:float)` parameter list; `x` stays a `Variable`. (Subtle detail from the parser comment on
`name`: "will resolve to Const later if needed".)

---

## 2. `lpl/` — the programming language (L_pl) and Python output

| File | Contents |
|---|---|
| `ast.py` | Five statement forms: `Assignment(variable, expr)`, `Skip`, `SequentialComposition(first, second)`, `IfElse(guard, then, else)`, `While(guard, body)`. Children are `MixNode = ProgramNode | Spec`, i.e. **a program may contain unrefined specs** — that is "L_mix" |
| `to_python.py` | `expr_to_python` (5), `to_python` (43). Maps `/\ → and`, `\/ → or`, `= → ==`, `<> → !=`, `~ → not`, `x0 → x0`; raises on `QuantifiedExpr` and on any leftover `Spec` ("Cannot execute unresolved Spec node") |

**Why it matters:** this is the *output* of the whole system. It is deliberately tiny so that
translating it to Python is obviously correct.

---

## 3. `refinement/` — the calculus engine

### 3a. `engine.py` (≈35 lines — read it, it's the heart)
`RefinementEngine.apply(spec, law_name, parameters)`:
1. looks up the law class in `self.laws` (a *per-engine copy* of the registry, so benchmarks can
   restrict the law set, `engine.py:17-22`),
2. instantiates it and calls `law.apply(spec, parameters)` → `RefinementResult`,
3. for each `obligation` calls `verify_obligation` and raises `VerificationError` on
   `FAILED`/`UNKNOWN` (the working tree adds a `VerificationUnknown` subclass at `engine.py:10`).

If `apply` returns normally, the step is **proved**. That is the whole trust boundary.

### 3b. `laws/` — one file per refinement law

| Law (registry key) | File | Terminal? | Details |
|---|---|---|---|
| `assignment` | `assignment.py` | yes | `x := E` |
| `skip` | `skip.py` | yes | do nothing |
| `initialized_skip` | `initialized_skip.py` | yes | skip with `x = x0` assumed |
| `sequential` | `sequential.py` | no | `[P,R] ; [R,Q]` |
| `flexible_sequential` | `flexible_sequential.py` | no | `[A,B] ; [C,D]` with three obligations |
| `alternation` | `alternation.py` | no | `if G … else …` |
| `iteration` | `iteration.py` | no | `while`, invariant = precondition |
| `initialised_iteration` | `initialised_iteration.py` | no | init ; `while` with LLM-given invariant |
| `strengthen_post` | `strengthen_post.py` | no | `[P,Q] ⊑ [P,R]` |
| `weaken_pre` | `weaken_pre.py` | no | `[P,Q] ⊑ [R,Q]` |

Support files:
* `base.py` — **`RefinementResult`** (`program` *or* `sub_specs`, plus `obligations` and `roles`),
  and the **`RefinementLaw`** abstract class with `PARAMS` (declares expected parameters),
  `apply`, and `build_program` (reassembles from children). The role names (`part1/part2`,
  `then/else`, `init/body`, `sub`, `body`) are how a recursive law labels its children.
* `registry.py` — the single table `LAWS` (line 28) plus `law_named`. **Adding a law = write a class,
  add it here, add a description in `llm/prompts.py:LAW_DESCRIPTIONS`** (a test,
  `tests/test_law_contract.py`, enforces that every law declares params and is described to the model).

Full mathematics of each law: `08a_Refinement_Calculus_Explained.md`.

### 3c. `frame.py` — "what may change"
Functions: `check_assignable` (rejects assigning to a rigid var, line 102), `rigid_conjuncts` /
`rigid_context` (carries unchanging precondition facts into sub-specs, 71/85), `obligation_params`
(gives frame vars their declared types so Z3 uses `Int` not `Real`, 55), `derive` (builds a
sub-spec that inherits the frame, 117). Its module docstring (lines 1–25) is a good short essay on
*why* this exists.

### 3d. `graph/` — the memory of the search
| File | Role |
|---|---|
| `node.py` | `RefinementNode(id, specification)` with `status` and list of attempt ids |
| `attempt.py` | `RefinementAttempt(id, source_node_id, law, parameters)` + `status`, `counterexample`, `error_message`, `destination_roles` |
| `status.py` | `AttemptStatus`: pending/running/**accepted**/**rejected**/**inconclusive**/error/**aborted**; `NodeStatus`: open/refining/**delegated**/**refined**/failed |
| `graph.py` | `RefinementGraph`: `create_node` (24), `record_attempt` (30), `is_complete` (92), `_assemble` (114), `reconstruct_mixed_program` (137), `reconstruct_program` (143) |

*Delegated* = split into sub-specs (not finished!); *refined* = turned into code.
`is_live` / `_inbound_map` make sure abandoned branches are ignored when checking completeness.

### 3e. `tree.py`
A small, older `RefinementNode` tree class (17 lines); the live code uses `graph/`.

---

## 4. `verification/`

* `proof_obligations.py` — a 17-line dataclass: `ProofObligation(assumptions, goal, params, description)`.
  Meaning: *assuming all of `assumptions`, `goal` must hold.*
* `z3_backend.py` — `verify_obligation` (58): translate, `solver.add(assumptions)`,
  `solver.add(Not(goal))`, `check()`; maps `unsat→PROVED`, `sat→FAILED(+counterexample)`,
  anything else `→UNKNOWN`. `describe_failure` (12) writes the message the LLM will read.
  `VerificationResult` constants at line 7. A 10 s timeout (`DEFAULT_TIMEOUT_MS`,
  override `FORMALLLM_Z3_TIMEOUT_MS`) is in the uncommitted working tree. `_plan` and `_solve` (2026-10-04): an
  obligation that times out is retried in up to four short runs, each rebuilt from scratch under its own random
  seed, before one patient run (`FORMALLLM_Z3_RETRIES=0` turns it off; `14`, §5f).

---

## 5. `llm/` — the model-facing layer

| File | Role |
|---|---|
| `provider.py` | `LLMProvider.generate(prompt, max_tokens)` interface; `MockProvider` (scripted answers for tests), `OllamaProvider` (local/remote Ollama), `OpenAIChatProvider` (OpenAI-compatible HTTP, with streaming, `_read_stream`); a `Spinner` for terminal UX |
| `prompts.py` | `to_string` (7: AST → text), `LAW_DESCRIPTIONS` (52), `LAW_ORDER` (74), `SYNTAX_HELP` (78), **`generate_state_prompt`** (92, single-turn), `generate_law_selection_prompt` (157) + `generate_parameter_synthesis_prompt` (206) for the optional two-turn mode |
| `parser.py` | Turning model text into `(law, parameters)`: `normalise_operators` (40, `&&→/\`…), `parse_expr` (58), robust JSON extraction `_load_json_key` (72), **`parse_llm_response`** (157), `parse_law_response` (198), `parse_parameters_response` (217) |

**Why the parser is long:** models wrap JSON in markdown, break backslashes, forget fields, emit
`None`. Each guard exists because of a measured failure (comments in the file cite model names).

---

## 6. `agent/refiner.py` — the control loop (read slowly)

`AutomatedRefiner(engine, llm, max_retries=5, max_depth=6, use_multi_turn=False)` (line 17).
Key state: `blacklisted_laws_per_node`, `param_failures_per_node`, `max_param_attempts = 2`.

`refine_node(graph, node_id, ancestry)` (67) pseudo-code:

```
for attempt in range(max_retries):
    if every law blacklisted for this node: break
    prompt   = state prompt (+ history of failures for this node)
    law, params = parse(LLM(prompt))                       # errors → AttemptStatus.ERROR
    skip if law is blacklisted
    attempt = graph.record_attempt(...)
    try   result = engine.apply(spec, law, params)         # runs Z3
    except VerificationError → REJECTED (counterexample stored) or INCONCLUSIVE ; retry
    if result is terminal (program)        → ACCEPTED, node REFINED, return True
    else:
        progress guards:  depth > max_depth      → REJECTED ("must use assignment/skip now")
                          sub-spec equals an ancestor → REJECTED ("no progress")
        create child nodes, mark node DELEGATED
        recurse on every child
        all ok → return True
        else   → ABORTED; count a parameter failure for (node, law);
                 after 2 such failures blacklist the law for this node
after loop: node FAILED; at root raise RefinementExhausted
```

Concepts to notice: **backtracking** (a law whose children fail is retried with new parameters,
then blacklisted), **history** (failure messages go back into the next prompt via
`_build_history_context`, 41), **progress guard** (prevents `strengthen_post` with `R = Q` from looping
forever; tests in `tests/test_progress_guard.py`).

---

## 7. `execution/` and `trace/`

* `execution/runner.py:run` (10) — for each `TestCase(inputs, expected)` builds a script, runs it
  with `subprocess` (isolated, timeout), collects the output variables, optionally evaluates the
  postcondition as Python. Returns `ExecutionResult(passed, failed, errors, timeout)`.
* `trace/serializer.py` — `graph_to_dict` (44), `export_graph_json` (80), `validate_trace` (84, a schema
  check), `export_graph_text` (130, the human trace `main.py` prints). Lets you replay *why* a program was produced.

---

## 8. `tests/` (what each file protects)

| Test file | Protects |
|---|---|
| `test_parser.py`, `test_walk.py`, `test_substitution.py` | the L_spec front end |
| `test_z3_backend.py` | proving / failing / timeout behaviour |
| `test_z3_restarts.py` | a timed-out run is retried from scratch under another seed; non-timeouts and caller-given limits are not |
| `test_assist.py`, `test_assist_pairs.py` | the leaf assist: one-line goals, equations solved for a variable, two assignments in a row; nothing unproved is ever returned; guesses are checked by Z3 whatever backend the run uses |
| `test_he_refine.py`, `test_he_oracle.py`, `test_evalplus_import.py` | the HumanEval pilot pipeline with a scripted model; the hand derivations of the pilot problems; EvalPlus is found even with `benchmarks/` first on the path |
| `test_law_contract.py` | every law declares params, is described to the LLM, emits the right obligations & roles |
| `test_engine_reachability.py` | **hand-written correct refinements still verify** (sqrt, counting loop, integer division). Docstring (1–16): these are regression tests, *not results* |
| `test_frame.py`, `test_progress_guard.py`, `test_fallback.py` | frames, no-progress detection, backtracking |
| `test_agent.py`, `test_llm_parser.py` | the loop with a `MockProvider`; JSON/operator parsing |
| `test_graph.py`, `test_mixed_program.py`, `test_trace_schema.py` | graph state, L_mix, JSON trace |
| `test_execution.py`, `test_integration.py`, `test_deliberate_failure.py` | runner; full pipeline; wrong refinements must be *rejected* |

Run: `python -m pytest FormalLLM/tests -q` → 425 passed and 19 skipped (444 collected) in the cloud workspace on 2026-10-05, with the v8 code (the skipped ones need Coq or Lean, which it does not have; on a machine that has them they run, and the session that wrote v8 reports all 444 passing). The count of 105 in the first version of this file is long out of date.

---

## 9. `benchmarks/` and the entry points

| File | Role |
|---|---|
| `cases.py` | the 13 specs: A1-skip, A2-assign, A3-assign-guarded, A4-impossible (negative control: no refinement exists), B1-sequential, B2-max, B3-abs, C1-sqrt-loose, C2-sqrt-tight, C3-loop-pinned, C4-loop-invariant, C5-sqrt-paper (paper's example), D1-intdiv. Each has `expected` (never shown to the LLM) and `test_cases` |
| `harness.py` | `run_trial`: `InstrumentedProvider` counts calls and enforces a **call budget**; records per-attempt outcomes |
| `run_bench.py` | CLI to run configs × cases × repeats (budget default 30, temperature 0.2); `CONFIGS` map names like `llama3.1`, `qwen3.5-think`, `ornith` to providers; core-law subset `CORE_LAWS` (line 14) |
| `baseline.py`, `baseline_cases.py` | the **direct** baseline: ask the model for plain Python (no calculus, no Z3), run it in a subprocess with timeout |
| `evaluate_models.py` | **Study 3**: same spec, two arms (`direct` vs `refinement`), code saved to `study_code*/` for side-by-side reading |
| `compare_laws.py` | core 5 laws vs extended 9 laws |
| `check_remote.py` | preflight: warm up hosted models before a run (cold start ≈163 s measured) |
| `manual_sqrt.py` | the sqrt refinement by hand (no LLM) |
| `results_viewer.py`, `viewer.html` | terminal / browser viewers for the `.jsonl` results |
| `reliability.py`, `reliability_batch.py` | the reliability study: one case many times / every other case in one go (resumable, with an impossible-spec control); `14`, `17` §3 |
| `replay.py`, `cross_check.py`, `summarize_reliability.py` | offline: re-derive stored trials from the model's raw replies; run the derived programs against the case's own specification; one summary table |
| `results/` | `*.jsonl` raw trials, `tables.md`, `baseline_tables.md`, `lawcmp_tables.md` |
| `study_code/`, `study_code_lenient/`, `baseline_code/` | the Python each model produced |

**Entry points:** `main.py <model>` (one hard-coded sqrt spec, 100 retries, prints final AST and trace);
`benchmark.py <model> <case_id>` (one case + execution against its test cases).
Environment switches: `FORMALLLM_STRICT_VARIANT` (default `1`: the loop body must also show
`0 ≤ V`; set `0` to require only decrease — an ablation, commit `32bf870`), and `FORMALLLM_Z3_TIMEOUT_MS`.

**`run_log_*.txt`** at the repo root are UTF-16 dumps of prompts/responses per model; read them with
an editor that understands UTF-16 (or `Get-Content -Encoding Unicode`).

---

## 10. "Where would I change X?"

| I want to… | Change this | Also touch |
|---|---|---|
| Add a new refinement **law** | new class in `refinement/laws/`; register in `laws/registry.py` | description in `llm/prompts.py:LAW_DESCRIPTIONS`/`LAW_ORDER`; test in `tests/test_law_contract.py`; a reachability test |
| Change **what the LLM is told** | `llm/prompts.py` (`SYNTAX_HELP`, `LAW_DESCRIPTIONS`, `generate_state_prompt`) | benchmark again — prompt edits change results |
| Support a **new model/provider** | subclass `LLMProvider` in `llm/provider.py` | add a config in `benchmarks/run_bench.py:CONFIGS` |
| Make parsing **more forgiving** of model output | `llm/parser.py` (`OPERATOR_ALIASES`, `_load_json_key`) | `tests/test_llm_parser.py` |
| Add **syntax** to the spec language | `lspec/grammar.lark`, `lspec/ast.py`, `lspec/parser.py` | `lspec/walk.py` registration, `z3_translator.py`, `lpl/to_python.py`, prompts' `to_string` |
| Change **how Z3 is used** (timeouts, tactics, logic) | `verification/z3_backend.py` | `tests/test_z3_backend.py`; refiner's INCONCLUSIVE handling |
| Swap Z3 for **another prover (Lean/Coq/…)** | replace `verify_obligation` behind the same `(status, message)` signature; translate `ProofObligation` instead of using `Z3Translator` | engine/refiner only see `VerificationResult` strings; keep that contract |
| Improve **failure feedback** to the LLM | `describe_failure` (`z3_backend.py:12`), `_build_history_context` (`agent/refiner.py:41`) | |
| Change **search/backtracking** policy | `agent/refiner.py:refine_node` (`max_retries`, `max_depth`, `max_param_attempts`) | `tests/test_fallback.py`, `test_progress_guard.py` |
| Change **frame** behaviour | `refinement/frame.py` | all laws call `derive` / `obligation_params` |
| Change **generated Python** | `lpl/to_python.py` | `tests/test_execution.py` |
| Add a **benchmark case** | `benchmarks/cases.py` (+ `baseline_cases.py` for the direct arm) | |
| Change **trace format** | `trace/serializer.py` | bump `TRACE_SCHEMA_VERSION`; `test_trace_schema.py` |

---

## 11. Suggested reading order (≈ 2 hours)

1. `lspec/ast.py` → `lpl/ast.py` (the vocabulary).
2. `refinement/laws/skip.py`, `assignment.py`, `sequential.py` (simplest laws) → `base.py`.
3. `refinement/engine.py` + `verification/z3_backend.py` (the trust boundary).
4. `tests/test_engine_reachability.py` (see it all work, no LLM).
5. `refinement/laws/initialised_iteration.py` (the hard one) with `08a` open beside it.
6. `agent/refiner.py` (the loop) and `llm/prompts.py`.
7. `benchmarks/evaluate_models.py` docstring + `results/`.

---

## 12. Common confusions

* **`Const` vs `Variable`.** `N` declared in `(N:float)` is a `Const` (input); `x` that is only free is a
  `Variable` (what the program sets). The split drives who may be assigned and what is rigid.
* **"Spec" appears inside programs.** `MixNode = ProgramNode | Spec`: half-finished programs are legal data.
* **Two `RefinementNode` classes.** `refinement/tree.py` (old) vs `refinement/graph/node.py` (used).
* **Law docstring vs behaviour.** `iteration.py`'s docstring (≈ lines 28–50) describes an *invariant
  parameter* but the code uses `invariant_expr = spec.precondition.expr` (line 66) and `PARAMS` has only
  `guard`/`variant` (line 51). The invariant parameter belongs to `initialised_iteration`. Trust the code.
* **Hidden global switches.** `os.environ` reads (`FORMALLLM_STRICT_VARIANT`, `FORMALLLM_Z3_TIMEOUT_MS`)
  change behaviour without appearing in function signatures.
* **"oracle" results.** Old tables (`results/tables.md`) include an "oracle" row; it was later
  removed as misleading (`benchmark.py:47-51`, `test_engine_reachability.py:1-16`). Don't quote it.

---

## 12b. What was added after this tour was written (2026-10-03)

This tour describes the code as it was on 2026-10-02. These files are new; where one contradicts the text above, trust the table.

| File | What it is |
|---|---|
| `llm/prompts.py`, `llm/law_cards.py`, `llm/spec_render.py` | the rebuilt, problem-independent prompts (`13`) |
| `refinement/feasibility.py` | every sub-specification a step creates must be feasible (`pre ⇒ ∃ frame. post`), else the step is refused with the exact values |
| `refinement/vocabulary.py` | a formula may only use the specification's own names |
| `agent/assist.py` | the optional leaf solver: closes one-line steps, solves a postcondition equation for a variable, closes a two-variable set-up or body with two assignments, and names the missing fact when the obvious step fails (`13`, §5.1 and §8) |
| `verification/backends/` | `z3`, `coq`, `lean`, `cross`, `fallback` (`z3+lean`), `process.py` (kills prover process trees) |
| `verification/certify.py` | re-checks every obligation of a finished derivation with Coq/Lean |
| `lspec/coq_translator.py`, `lspec/lean_translator.py` | obligations printed as Coq / Lean (Booleans as `Prop`) |
| `lspec/evaluator.py` | evaluates specifications on concrete values (checks a hand-written spec against a reference solution) |
| `lpl/typed_python.py` | emits Python that means what the prover meant (`//` for integer division) |
| `main.py` | one command from specification to a certified program |
| `benchmarks/reliability.py`, `summarize_reliability.py`, `replay.py` | repeated trials with confidence intervals; one table of many studies; offline re-derivation |
| `benchmarks/classic.py` | the Table-7 analogue |
| `benchmarks/datasets/` | HumanEval/EvalPlus loading and portable test runner, the direct baseline, 12 checked formal specs, the refinement pilot (`he_refine.py`), and `he_oracle.py`: hand derivations of eleven of them, run through the engine and the real tests with no model |

## 12c. What was added by 2026-10-05 (code v8)

This is the code the overnight studies ran (note `10`, newest entries); it was copied into this folder at about 00:55 UTC on 2026-10-05. Each description comes from the file's own header. Where one contradicts the text above, trust this table.

| File | What it is |
|---|---|
| `llm/spec_render.py` (changed) | shows the model each formula exactly as the engine reads it: parentheses that change the value under whole-number division are kept (`n = 2 * (n / 2)` used to be shown as `n = 2 * n / 2`); `tests/test_spec_render.py` renders 300 random formulas, reads them back and checks that they compute the same values |
| `refinement/value_kinds.py` | refuses a step that puts a number into a truth value (or the reverse, or a real into an integer): `b := 0` for a Boolean `b` used to be *proved*, because Z3's Python interface turns `false` into 0 |
| `refinement/relevance.py` (extended), `refinement/engine.py` | besides refusing a test on a variable whose starting value is arbitrary, the test of an `if` or `while` must be something Python can run (no quantifier); the refusal points to a loop with the quantifier in its invariant |
| `lspec/z3_translator.py`, `lspec/evaluator.py`, `lspec/grammar.lark`, `llm/parser.py` | Z3 now divides whole numbers rounding down like Python, Coq and Lean (`7 / -2` used to be -3 in Z3 and -4 elsewhere); arrays of floats are modelled as floats; array indices may be expressions (`l[k + 1]`); `forall k:int (...)` and `A -> B` are read the way models write them |
| `agent/assist.py` (changed) | proposes `true` and `false` for Booleans and `l[i]` reads for numbers; the two-assignment search is limited by prover queries (1000) rather than seconds (a 20-second limit stays as a safety net) |
| `benchmarks/datasets/he_specs.py`, `he_oracle.py` (changed) | 20 checked specifications (`python benchmarks/datasets/he_specs.py` checks them against the reference solution and counts the wrong answers each one rejects); hand derivations of 17 of them (14 pass every test here; `gcd`, `is_prime` and `iscube` are too slow for EvalPlus or time out) |
| `benchmarks/pilot_compare.py` | one table row per pilot problem (model alone, hand derivation, old and new code); for all 106 runs give it the three v8 pilot files with `--new` (`17`) |
| new tests | `test_spec_render.py`, `test_quantifier_syntax.py`, `test_value_kinds.py`, `test_executable_guards.py`, `test_z3_semantics.py`; 444 tests in all |

---

## 13. Check yourself

1. Which single method decides whether a refinement step is *trusted*? Which file is it in?
2. A law returns a `RefinementResult` with `sub_specs` but no `roles`. What happens, and where is that enforced?
3. Trace what happens, file by file, when the LLM answers `{"law":"assignment","parameters":{"variable":"N","expr":"0"}}` for a spec whose frame is `x`.
   *(Answer: parse → engine.apply → `check_assignable` raises `FrameViolation` before any Z3 call → the
   refiner treats the exception as an ERROR attempt.)*
4. Where would you add logging of every Z3 query? Where would you swap in Lean?
5. Why are `test_engine_reachability.py` results "not allowed to be quoted as a result"?
6. What is the difference between `NodeStatus.DELEGATED` and `REFINED`?
7. Which two things stop the refiner from recursing forever?
