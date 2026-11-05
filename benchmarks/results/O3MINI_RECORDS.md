# o3-mini run and prover-gap records

Everything produced while measuring o3-mini on the Lean engine and closing the prover gaps it exposed
(2026-10-21 to 2026-11-05). The prover code itself is on branch `o3run`; this branch holds the data.

| Folder | What it holds |
|---|---|
| `lean_agent/` | The logged o3-mini runs: `full_lean_specs_o3-mini.jsonl` (156 HumanEval tasks, 85 solved), `full_verina_o3-mini.jsonl` (158 Verina tasks, 61 solved), and the smaller A/B, ladder and measurement runs |
| `o3mini_gap_replay/` | The gap replays. `gate_b.py` re-judges o3-mini's logged replies against the current prover; a *gap* is a step that is still unproved and has no counterexample. `gbN_*.jsonl/.log` are replay rounds, `gapN_*.txt` the task lists, `regressN/` the 25-task lemma regression after each prover change, `nightN.sh` / `nightN.out` the scripts and their output, `draftN_*` the lemma and tactic drafts that became commits on `o3run` |
| `o3mini_workbench/` | Probes and scratch Lean files used to find each gap, lemma drafts, launch and status scripts, the Verina task copies (`vtasks/`), and `ctrl_results/` + `ctrl_uncommitted.patch` (the control arm's results and its uncommitted provider/run_bench edits) |

Prover commits on `o3run` that these records back: d94879d, 0857e61, b557f88, 358e60d, c3b0530.
