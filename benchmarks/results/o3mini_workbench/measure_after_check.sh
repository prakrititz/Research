#!/bin/bash
# Gate: the free check of every HumanEval+classic hand-written derivation must pass with zero refusals.
# Only then the paid measurement: 20 untouched solvable HumanEval tasks, all fixes, hard $1 cap, stop after 2 unsolved.
S="/c/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
F="$S/fix/pc_he.jsonl"
until [ "$(grep -vc '"outcome": "SOLVED"' "$F")" -gt 0 ] || [ "$(wc -l < "$F")" -ge 164 ]; do sleep 20; done
refused=$(grep -vc '"outcome": "SOLVED"' "$F")
if [ "$refused" -gt 0 ]; then
  echo "GATE FAILED: $refused correct answer(s) refused by the framework; no paid run started"
  grep -v '"outcome": "SOLVED"' "$F" | cut -c1-700
  exit 1
fi
echo "GATE PASSED: $(wc -l < "$F")/164 correct answers accepted; starting the capped measurement"
cd "$S/rc2"
PYTHONIOENCODING=utf-8 FORMALLLM_FIXES="2,3,4,5,6" python -u benchmarks/lean_agent_run.py run --config gpt-5.4-mini \
  --dataset humaneval --repeats 1 --budget 20 --imports "import Mathlib" --max-usd 1 --stop-after-exhausted 2 \
  --tasks $(cat "$S/measure20.txt") --out measure20.jsonl > "$S/ladder/measure20.log" 2>&1
echo "MEASUREMENT DONE"
grep -E " trial |stopping|Traceback" "$S/ladder/measure20.log" | cut -c1-140
grep "Cumulative" "$S/ladder/measure20.log" | tail -1 | grep -oE 'Cumulative Total: .[0-9.]+'
