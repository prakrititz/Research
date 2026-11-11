# Handoff — 2026-11-08 (moving to a new machine)

> **Update 2026-11-11:** [`HANDOFF_VERINA.md`](HANDOFF_VERINA.md) has the current run status and the Verina fix plan.
> It includes a `wit_search` name clash that breaks Verina. Read it next.

Everything needed to continue on a fresh machine, with no memory of earlier sessions. Read this first, then
[`Reading Material/29_LSpec_Workflow.md`](Reading%20Material/29_LSpec_Workflow.md) (how the L_spec workflow works) and
`Reading Material/22`–`27` (the Lean core). Standing rules for Claude Code are in [`CLAUDE.md`](CLAUDE.md).

## 1. The goal

Match or beat **Refine4LLM: 150/164 HumanEval** with an automated refinement prover. The model only chooses laws and
writes their parameters in L_spec; **it never writes proofs**. Lean proves every obligation, and a task counts as solved
only when its finished Lean file compiles in a fresh process with standard axioms, the dataset's own statement, and all
tests true.

## 2. Where things are

| what | where |
|---|---|
| branch | `main` (fast-forwarded from `lspec` on 2026-11-08; `lspec` is identical) |
| Lean engine (laws, obligations, tactic cascade, certificate) | `FormalLLM/lean/engine.py`, `laws.py`, `session.py` |
| proved library lemmas the cascade uses (`Refine.*`) | `FormalLLM/lean/lemmas.py` |
| loop counter-examples by running the loop | `FormalLLM/lean/dynamic.py` |
| L_spec ↔ Lean translator | `FormalLLM/dsl/lspec_syntax.py`, `lean_syntax.py`, `steps.py`, `defs.py`, `ops.py` |
| repairs (conversions Lean needs, typos) | `FormalLLM/dsl/repair.py` |
| feedback to the model, prompts, worked examples | `FormalLLM/dsl/feedback.py`, `prompts.py`, `examples.py` |
| the end-to-end model loop | `FormalLLM/lean/lspec_agent.py` (`LSpecAgent`, `judge`, `GoldModel`) |
| runners | `benchmarks/lspec_run.py` (whole tasks), `benchmarks/lspec_applier.py` (one step per gold goal) |
| translation checks | `benchmarks/lspec_steps.py`, `lspec_equiv.py`, `lspec_specs.py` |
| fresh-process verifier | `benchmarks/verify_derivations.py` (used by `lspec_run.py` for every finished task) |
| hand-written derivations (gold) | `exports/all_derivations.json` (humaneval 159, classic 5, verina 177) |
| results | `benchmarks/results/lspec/` (`run_*.jsonl`, `verified/*.lean`) |
| remote model server check | `benchmarks/remote_check.py` |

## 3. Setting up the new machine

```bash
git clone -b main https://github.com/prakrititz/Research.git Symbolic_LLM_new
```
`-b main` matters: the GitHub default branch is `o3run`, so a plain clone checks out the wrong branch (or set the
default to `main` in the repository's settings).

Versions matter: **Lean 4.34.1, Mathlib tag `v4.34.1`**, REPL `leanprover-community/repl` (commit `193cf4b`, "bump
toolchain to v4.34.0") with its `lean-toolchain` set to `leanprover/lean4:v4.34.1`.

```bash
# 1. elan (Lean's installer) into ~/.formalllm/elan
export ELAN_HOME=~/.formalllm/elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
export PATH=$ELAN_HOME/bin:$PATH

# 2. a Lake project requiring Mathlib v4.34.1 in ~/.formalllm/lean-env-parent/lean-env
mkdir -p ~/.formalllm/lean-env-parent && cd ~/.formalllm/lean-env-parent
lake +leanprover/lean4:v4.34.1 new lean-env math
cd lean-env
echo 'leanprover/lean4:v4.34.1' > lean-toolchain
#   in lakefile.toml, the mathlib [[require]] must have:  rev = "v4.34.1"
lake update && lake exe cache get          # downloads compiled Mathlib (no compiling); several GB

# 3. the REPL in ~/.formalllm/repl
cd ~/.formalllm && git clone https://github.com/leanprover-community/repl && cd repl
git checkout 193cf4b && echo 'leanprover/lean4:v4.34.1' > lean-toolchain && lake build

# 4. Python 3.10+ packages (there is no requirements.txt yet, despite the README)
python -m pip install lark z3-solver pytest evalplus certifi
#   macOS python.org builds:  export SSL_CERT_FILE=$(python3 -m certifi)
```

Other locations can be set with `FORMALLLM_ELAN_HOME`, `FORMALLLM_LEAN_PROJECT`, `FORMALLLM_LEAN_REPL`. Useful knobs:
`FORMALLLM_LEAN_IMPORTS` (default `import Mathlib`), `FORMALLLM_LEAN_MAX_GB` (restart the REPL above this, default 6).

**Credentials** (create by hand; never commit, never print):
* `~/.formalllm/remote_auth`: one line `user:password` for the remote gpt-oss server (HTTP Basic). Change that
  password: it was once pasted into a chat.
* `~/.formalllm/openai_key`: only for paid OpenAI runs; it is sent to `api.openai.com` and nowhere else.

**Check the setup**, in this order (each must pass before the next):

```bash
python -m pytest -q FormalLLM/tests/test_lspec.py FormalLLM/tests/test_remote_endpoint.py   # 110 tests
python benchmarks/lspec_steps.py --dataset humaneval --no-lean        # 381 steps translate both ways (no Lean)
python -m pytest -q FormalLLM/tests/test_lean_dynamic.py              # 8 tests, starts Lean with full Mathlib
python benchmarks/lspec_steps.py --dataset humaneval                  # 381 steps identical in Lean
python benchmarks/lspec_run.py --dataset humaneval --model gold --only he_002_truncate_number --attempts 1 --retractions 0
                                                                      # SOLVED verified=True
```

## 4. State on 2026-11-08

**Translation: verified in full.** All hand-written derivations go to L_spec and back with Lean confirming the
meaning is unchanged: steps 381/11/323, derivations 159/5/177, definitions 390/10/399 (HumanEval/classic/Verina).

**Repairs:** on the saved qwen3.5 replies (probe v6, 198 steps, re-checked with no model calls) accepted 151 → 159,
at the first attempt 102 → 140, 0 lost. Added since, not yet measured on the replay: the `}`-for-`)` typo rule, the
"your reply was cut off" message, the `indexOf`/`sorted`/`len` method spellings.

**End to end with the gold steps** (`benchmarks/results/lspec/run_humaneval_gold_*.jsonl`, first 20 HumanEval tasks):

| run | result |
|---|---|
| strict (no helper lemmas), joint | **18/20** solved and verified in a fresh process |
| the 2 strict failures (he_001, he_020) with `--lemmas` | 2/2 solved: blocked only by helper lemmas (§5.3) |
| split workflow, he_000–he_002 | 2/3 (he_001 needs its lemmas, as in joint): split works end to end |

Time per task after the speed fix: 1–6 minutes (58–357 s) including the fresh-process check, against 5–60 minutes
before.

**Update 2026-11-09 — strict gold on all 159 HumanEval tasks: 150/159** solved and verified in a fresh process
(`run_humaneval_gold_v3_joint.jsonl`; 135/159 before the prover work below). Still failing: he_001, 025, 059, 071,
087, 099, 111, 114, 129 (paren groups, prime factors, rounding a square root / a decimal, nested flatMap, foldl
min/max over a computed list). What was added (`engine.py` `_shape_tactics`, `lemmas.py`):
* `wit_search`: existential goals by trying the context's variables, the goal's own terms, successors, 0/1/2; either
  side of `∨`; binders introduced; each choice closed cheaply or by a budgeted `grind`;
* members turned into indices in the hypotheses too, then `grind`; closed forms split conjunct by conjunct after
  unfolding only the pre/postcondition; the task's non-recursive helpers unfolded; induction along its recursive ones;
* library: binary numerals of `Nat.toDigits 2`, sorts by a key then the order, `idxOf` of a member, letter/digit
  classes decided on their codes (`lower_cases` & co., kept out of `lib_apply`), `lib_apply` side goals by `decide`;
* speed: the library imported from the compiled module `LeanEnv.RefineLib`, an obligation cache
  (`~/.formalllm/cache/obligations.sqlite`, `FORMALLLM_CACHE=0` turns it off), fresh-process checks after the run
  (`--file-check end`, default); `benchmarks/lean_probe.py dump|serve` to work on refused obligations.

**Model runs:** a free local check passed (`--model ollama:gemma4`, he_002 and he_003: 2/2 solved and verified,
`run_humaneval_ollama-gemma4_smoke_joint.jsonl`). On the Mac, `z3-solver` had to be installed (the model path imports
it) and `~/.formalllm/remote_auth` does not exist yet: create it before a remote run. `python benchmarks/remote_check.py`
tells whether the remote server is up.

## 5. Fixing the prover: what to do, in order

### 5.1 Speed — main cause found and fixed (2026-11-08)

**Cause:** the engine's lemma library (`lemmas.py` + `AUTO_CLOSE`, ~140k characters) was elaborated again in every
call that built an environment: the task's environment (~80 s), the REPL certificate (~85 s), its tests (~85 s), and
again for each helper lemma, plus once more in the fresh-process check. Profile of he_002 (one step): 246 s in Lean,
**0.2 s** of it proving its obligation.

**Fix:**
* `LeanSession.library_env(text)` elaborates the library once per REPL process (again after a restart); a task's
  environment and its certificate are built on top of it (`Derivation._library_env`, `source(library=False)`).
* The fresh-process check imports the library from a compiled module, `LeanEnv/RefineLib.lean` in the Lean project
  (`lspec_run.library_module`, built by `lake build LeanEnv.RefineLib`, rebuilt only when the text changes).

**Result** (same session): he_002 steps 0.3 s + certificate 11 s (was 76 s + 170 s); he_000 (5 steps) 2.3 s + 14 s;
end to end with the fresh-process check, he_002 50 s (was 334 s), file check 39–46 s (was ~110 s). What is left per
task is mostly Mathlib's import in the fresh process (~40 s) and the one-time library load (~85 s per REPL start).

**Remaining ideas**, if needed:
* start the REPL with `import LeanEnv.RefineLib` too (`FORMALLLM_LEAN_IMPORTS`), so even the one-time 85 s goes;
* run the fresh-process checks of finished tasks in parallel with the next task (they are separate processes; watch
  memory: each holds ~3 GB);
* the earlier ideas below, for tasks whose obligations really are slow.

Where to measure, for a slow task:

* per obligation: `Derivation.lean_seconds` is the total; add per-verdict timing around the proving in `engine.py`
  (the cascade `_cascade_groups`, line ~164; the generic closers and `try?`, lines ~544–558);
* the knobs: `Derivation(timeout=90.0)` per obligation, `PORTFOLIO_TIMEOUT = 600.0` (engine.py:150) for the slow
  portfolio, counter-example search (`counterexamples=True`) and `dynamic.loop_finding` on refused steps;
* likely wins: stop a cascade at the first closer that works (check it does), cache Lean environments per task (the
  per-step harness already loads the library once, `lspec_equiv.base_env`), skip `try?` when a cheaper closer proved
  the same obligation shape before.

### 5.2 A cache of proved obligations

Every run proves the same obligations again (gold, ablations, repeated trials). Key the cache on a hash of: the lemma
library text (`lemmas.py`), the task prelude, the helper lemmas' text, the obligation statement and the tactic used;
store proved / not proved with the Lean version; drop entries when any of those change. A cached "proved" must still
be re-checked by the final fresh-process compile (it is: `lspec_run.file_check`), so a stale entry can never produce a
wrong SOLVED.

### 5.3 The strict ceiling (helper lemmas)

49 of 159 HumanEval and 97 of 177 Verina gold derivations bring helper lemmas. Under the strict rule the model cannot
supply them, so those tasks are capped unless the prover finds the facts itself.

1. Run strict gold on all 159 (`--attempts 1 --retractions 0`), then `--lemmas` on the failures: the difference is the
   list of tasks blocked only by helper lemmas.
2. For each, find the obligation that fails (the row's `steps[*].feedback` shows it in L_spec) and the gold lemma that
   closes it (`exports/all_derivations.json`, the node's `lemmas`).
3. Generalize it into `FormalLLM/lean/lemmas.py` as a `Refine.*` lemma (and into `SIMP_SET` / `EVAL_SET` if it is a
   rewrite); the file's comments show this was done before (he_009, he_005, he_034, the `foldl max` family).
4. Re-run strict gold on those tasks. Report the ceiling as "solved strictly / 159".

### 5.4 Long REPL sessions

The REPL slows down and grows over a long run. `lspec_run.py` now decides SOLVED by the fresh-process compile, and
calls `lean.recycle()` between tasks (restart above `FORMALLLM_LEAN_MAX_GB`). If tasks still time out late in a run,
lower that limit or restart the REPL before each task's certificate.

## 6. After the prover: model runs

```bash
python benchmarks/remote_check.py                                   # up? which models?
python benchmarks/lspec_run.py --dataset humaneval --model remote:gpt-oss-120b --workflow joint --limit 20
python benchmarks/lspec_run.py --dataset humaneval --model remote:gpt-oss-120b --workflow split --limit 20
#   ablations: --no-repair, --examples 2, --samples 3, --max-binds 3 (default)
python benchmarks/lspec_applier.py --dataset humaneval --model replay:<results.jsonl> --level elaborate
#   re-checks saved replies after any translator change, without the model
```

Paid hosts (OpenAI, OpenRouter, ...) refuse to start without `--max-usd <cap> --paid-ok`; only run them after the
owner approves the cap.

## 7. Pitfalls already hit

* Windows: editing Python files with a bash heredoc that contains `\n` inside strings silently fails to match; use an
  editor or a Python script file. PowerShell `Get-Content | python` adds a BOM to JSON lines: read files in Python.
* Windows paths for Python: pass `C:/...`, not `/c/...`.
* Run one Lean-heavy job at a time (each REPL holds 4–6 GB with Mathlib); the full pytest suite starts several.
* The shared test fixture (`FormalLLM/tests/conftest.py`) imports only part of Mathlib; tests that build a
  `Derivation` need `FULL_IMPORTS` (see `test_lean_dynamic.py`), otherwise "unknown tactic".
* `GoldModel` answers the same step every time: use `--attempts 1 --retractions 0` for gold runs.
