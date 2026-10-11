# 17 — Cookbook: how to run every piece

> Every command below was run on this machine (Windows 11, Git Bash). Replace the folder if yours differs. Nothing here needs administrator rights. **Do not put the hosted model's password in any file inside the repository**; the commands read it from your user folder.

All commands are run from the repository folder: `C:\Users\Prakrititz Borah\Downloads\Work\Research\Symbolic_LLM`.

---

## 0. One-time setup (already done on this machine)

| What | Where | Check it works |
|---|---|---|
| Python 3.11 + packages | `pip install -r FormalLLM/requirements.txt`, plus `evalplus datasets pypdf` | `python -m pytest FormalLLM/tests -q -k "not lean and not coq"` → all pass |
| Rocq (Coq) | `C:\Users\Prakrititz Borah\.formalllm\rocq` | `export PATH="$HOME/.formalllm/rocq/bin:$PATH"; coqc --version` |
| Lean 4 + Mathlib | `…\.formalllm\elan`, `…\.formalllm\lean-env-parent\lean-env` | `python -m pytest FormalLLM/tests/test_backend_lean.py -q` |
| Hosted model login | one line `user:password` in `C:\Users\Prakrititz Borah\.formalllm\remote_auth` (outside the repository) | see §2 |

Before any command that talks to the hosted model, run **once per terminal**:

```bash
export FORMALLLM_REMOTE_AUTH="$(cat "$HOME/.formalllm/remote_auth")"
export PATH="$HOME/.formalllm/rocq/bin:$PATH"       # so Coq can be found
```

---

## 1. Run the whole test-suite (no model needed)

```bash
python -m pytest FormalLLM/tests -q -k "not lean and not coq"    # fast: about 15 s
python -m pytest FormalLLM/tests -q                                # everything, including Coq and Lean: about 2 min
```

---

## 2. Derive a verified program: the one-command version

```bash
python main.py --case C5-sqrt-paper --config gpt-oss-120b-low --assist --certify coq lean --run N=10,e=1
```

What you see: the specification (readable), the model's steps as they happen, then

```
SUCCESS: 2 LLM call(s), 2 step(s) closed by the prover alone, 12 s
Derived program (every step proved):
x = 0
while (N >= ((x + e) * (x + e))):
  x = (x + e)
Running on N=10,e=1:  {'x': 3}
Independent check by proof assistants:
  coq: 3 of 3 certified ... lean: 3 of 3 certified ...
```

| Option | Meaning |
|---|---|
| `--case ID` / `--spec FILE` / `--spec-text "…"` | which specification (`--list-cases` shows the built-in ones) |
| `--config NAME` | the model: `gpt-oss-120b-low` (default, ≈ 7 s per call), `-medium`, `-high`, `qwen3-coder-next`, or a local Ollama model |
| `--assist` | let the prover close one-line steps and tell the parent which fact is missing (**not in the paper**; see `13`) |
| `--strict 0/1` | `1`: a loop variant must also stay ≥ 0; `0`: it must only decrease (the paper's Lemma 6.7) |
| `--backend` | what proves each step: `z3` (default), `coq`, `lean`, `cross-coq`, `cross-lean` |
| `--certify coq lean` | after success, have these re-check every obligation of the derivation |
| `--proofs DIR` | keep the generated `.v` / `.lean` files |
| `--json FILE` | write a machine-readable summary (never contains the password) |

---

## 3. How reliable is it? The reliability study

```bash
python benchmarks/reliability.py --config gpt-oss-120b-low --trials 30 --turns 2 --budget 30 \
       --strict 0 --assist --certify coq --label my_run
```

Writes one JSON line per trial to `benchmarks/results/reliability/my_run_<time>.jsonl` and prints a summary with the Wilson 95 % interval. Each trial keeps every raw model reply. Results and their meaning: `14`.

**Replay a stored study offline** (no model, no network; the same replies must give the same program):

```bash
python benchmarks/replay.py "benchmarks/results/reliability/v5_relaxed_assist_*.jsonl" --assist --strict 0 --certify coq
```
It prints `same` or `DIFFERENT` for every trial and a count. A `DIFFERENT` row means the code changed after that row was recorded.

**The other benchmark cases, all at once** (the square root has been measured about 260 times; the other 12 cases have not).

**On Windows, the easy way:** double-click `run_other_cases.bat` in the repository folder. It reads the login from your user folder (it is never printed), puts Coq on the PATH, and runs the command below; from a terminal it accepts the same options, for example `run_other_cases.bat --cases A2-assign --trials 2` for a one-minute check.

```bash
python benchmarks/reliability_batch.py --dry-run          # show the plan and the commands, call nothing
python benchmarks/reliability_batch.py --trials 20        # 11 solvable cases x 20 trials + the impossible control x 5
python benchmarks/reliability_batch.py --cases B2-max C4-loop-invariant --trials 10
```
Measured on the first full run: the easy cases and the loop cases took about 2 to 5 minutes each (20 trials, 2 to 4 model calls per trial); integer division, where every trial ran out of its 30 calls, took about 3.7 minutes *per trial*. Same settings as the v5/v6 studies (relaxed rule, assist on, 30 calls, Coq certification). Before each case it makes one tiny model call; if the model cannot be reached the batch stops at once, instead of spending hours on trials that never get an answer (`--no-preflight` turns the check off). The impossible control runs last. Ctrl-C is safe: each trial is saved when it finishes and the same command resumes. Roughly 45 minutes to 1.5 hours if each trial takes the square root's ~12 s (an estimate; simpler cases should be faster, and the control case runs every trial to its call limit). At the end it writes `benchmarks/results/reliability/cases_summary.md` (success per case with 95 % intervals) and `cases_cross_check.txt`. `A4-impossible` is a negative control: **any success there prints a SOUNDNESS ALERT**, because the specification cannot be met.

**Re-measure integer division after the assist fix (Windows: double-click `run_v7_check.bat`).** It runs `reliability_batch.py --prefix v7 --cases D1-intdiv A4-impossible` (20 trials of integer division, then the 5-trial impossible-spec control), writes files starting with `v7_` so they never mix with the earlier `cases_` files, and ends with `v7_summary.md` and `v7_cross_check.txt`. About 6 minutes for the division, about 15 for the control. The same command works from a terminal with any other `--prefix` to keep a new code version's results apart.

**Do the proved programs also run correctly?** (no model, no network)

```bash
python benchmarks/cross_check.py "benchmarks/results/reliability/v6_relaxed_assist_*.jsonl" --random 200
```
Runs each stored derived program on the baseline's hard-coded inputs (plus random ones) and checks it against the case's own formal specification and the old baseline's checker. `14`, §5c.

**Reading a summary table.** `trials` counts every trial; `success` is judged only on trials that reached the model. A trial whose every call failed to connect is `NETWORK` (shown under "other outcomes", not counted against the method).

---

## 4. The paper's other experiments

| Paper | What | Command | Doc |
|---|---|---|---|
| Table 7 (CorC programs) | steps and proof time, core laws vs extended laws, four classic programs | `python benchmarks/classic.py --certify lean` | `15`, `16` |
| Table 6, baseline rows | the model writes each of the 164 HumanEval functions directly | `python -m benchmarks.datasets.direct_baseline --config gpt-oss-120b-low --out baseline.jsonl` | `16` |
| (ours) | re-score stored baseline answers offline, no model | `python -m benchmarks.datasets.direct_baseline --reevaluate benchmarks/results/datasets/direct_baseline_gpt-oss-120b-low.jsonl` | `16` |
| Table 6, Refine4LLM rows | derive-then-test on the pilot subset | `python -m benchmarks.datasets.he_refine --config gpt-oss-120b-low --repeats 3 --assist --out pilot.jsonl --baseline baseline.jsonl` | `16` |
| (ours) | check that each formal HumanEval specification is right | `python -m benchmarks.datasets.he_specs` | `16` |
| (ours) | the pilot's ceiling: hand derivations of eleven of the twelve problems through the engine and the real tests, no model | `python -m benchmarks.datasets.he_oracle` | `16` |
| Sanity | the test harness accepts the reference solutions | `python -m benchmarks.datasets.humaneval` (164/164) | `16` |

**The HumanEval pilot on Windows: double-click `run_humaneval_pilot.bat`** (12 problems, 3 tries each, the direct baseline printed beside it; the login is read from your user folder and never printed). It accepts the same options as `he_refine`, so `run_humaneval_pilot.bat --tasks A --repeats 1` is a few-minute check of tier A, and `run_humaneval_pilot.bat --tasks C --backend z3+lean` runs the hardest tier with Lean as the fallback for goals Z3 cannot decide. A try whose every model call failed to connect is labelled `NETWORK`, not counted as a failure, and run again next time; progress is saved after every try, so closing the window is safe. What to expect: `16`, §5.2.

**Z3 and luck.** Z3's running time on a hard obligation is very uneven, so the prover retries a timed-out obligation in up to four short runs from scratch (`FORMALLLM_Z3_RETRIES=0` turns that off; `FORMALLLM_Z3_TIMEOUT_MS` changes the 10 s limit). `14`, §5f.

---

## 5. Looking at what happened

| I want to see | Do this |
|---|---|
| the model's exact prompts and answers for a run | `reliability.py … --transcripts DIR` writes `trial_NN.txt` files |
| the derivation tree of a run | `main.py` prints it at the end; or `FormalLLM/trace/serializer.py` |
| why a trial failed | open its transcript; the lines `---> [Refining Node 'N4' …]` show which node the calls went to |
| the proof files Coq / Lean checked | `main.py … --proofs DIR` |

---

## 6. If something goes wrong

| Symptom | Likely cause | Fix |
|---|---|---|
| `coqc is not installed` in a certificate | PATH does not include Rocq | the `export PATH=…` line in §0 |
| every trial shows `BUDGET` or `NETWORK` after a few seconds | the hosted model is unreachable (`NETWORK` = every call failed to connect; those trials are not counted against the method) | `curl -u "$FORMALLLM_REMOTE_AUTH" -H "ngrok-skip-browser-warning: 1" "<URL>/v1/models"` should answer `200` |
| Lean takes minutes | first use after reboot (Mathlib loading from disk) | wait; later runs take ≈ 10 s |
| `UnicodeEncodeError` printing | Windows console code page | `export PYTHONIOENCODING=utf8` |
| a study seems stuck | a long trial (30 model calls can take 5–7 minutes) | look at the newest file in the transcripts folder |
