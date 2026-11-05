#!/bin/bash
# A/B on a random sample of originally-exhausted tasks: control = old agent/engine, new = Antigravity's edits. 3 repeats each.
S="/c/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
export PYTHONIOENCODING=utf-8 FORMALLLM_MAX_BUDGET_USD=15
mkdir -p "$S/ab"
for arm in ctrl rc2; do
  for set in he ve; do
    if [ $set = he ]; then ds=lean_specs; else ds=verina; fi
    ( cd "$S/$arm" && python -u benchmarks/lean_agent_run.py run --config gpt-5.4-mini --dataset $ds --repeats 3 --imports "import Mathlib" \
        --tasks $(cat "$S/sample_$set.txt") --out "ab_${set}.jsonl" > "$S/ab/${arm}_${set}.log" 2>&1 ) &
  done
done
wait
echo ALL_DONE
