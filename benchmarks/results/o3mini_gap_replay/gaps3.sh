#!/bin/bash
# Gate B on the trials o3-mini lost with at least one step the prover did not prove (gap_<set>.txt): HumanEval, then Verina.
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
for set in lean_specs verina; do
  for round in $(seq 1 30); do
    # a fresh process every 4 trials (Lean memory does not pile up)
    python -u "$S/fix/gate_b.py" "$S/rc2" "benchmarks/results/lean_agent/full_${set}_o3-mini.jsonl" "$S/fix/gb3_${set}.jsonl" \
      --limit 4 --only $(cat "$S/fix/gap3_${set}.txt") > "$S/fix/gb_round.log" 2>&1
    cat "$S/fix/gb_round.log" >> "$S/fix/gb3_${set}.log"
    left=$(head -1 "$S/fix/gb_round.log" | awk '{print $1}')
    [ "$left" = "0" ] && break
  done
  echo "GATE B $set done"
done
echo GAPS3 DONE
