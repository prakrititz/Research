#!/bin/bash
# Cumulative ablation ladder on the 16 dev tasks. R0 = old code (ctrl tree); R1 = fix 1 (engine tactics, syntax budget,
# no charge for engine timeouts); R2 = +Lean grounding & library card; R3 = +name hints; R4 = +worked examples; R5 = +proof sub-agent.
S="/c/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
export PYTHONIOENCODING=utf-8 FORMALLLM_MAX_BUDGET_USD=8
mkdir -p "$S/ladder"
TASKS=$(cat "$S/dev_tasks.txt")
rung() {  # name tree fixes
  ( cd "$S/$2" && FORMALLLM_FIXES="$3" python -u benchmarks/lean_agent_run.py run --config gpt-5.4-mini --dataset lean_specs \
      --repeats 1 --budget 20 --imports "import Mathlib" --tasks $TASKS --out "ladder_$1.jsonl" > "$S/ladder/$1.log" 2>&1 )
}
rung R0 ctrl "" & rung R1 rc2 "" & wait
rung R2 rc2 "2" & rung R3 rc2 "2,3" & wait
rung R4 rc2 "2,3,4" & rung R5 rc2 "2,3,4,5" & wait
echo LADDER_DONE
