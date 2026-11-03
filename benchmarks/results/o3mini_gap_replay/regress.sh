#!/bin/bash
# Regression of everything HumanEval + classics closed before: (a) the lemma tasks closed earlier, prover alone, one task per
# process; (b) every certified derivation through the agent (pipeline check), resumable.
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
mkdir -p "$S/fix/regress"
for t in $(cat "$S/fix/closed_lemma_he.txt"); do
  [ -s "$S/fix/regress/$t.jsonl" ] && continue
  python -u benchmarks/prover_ceiling.py --dataset humaneval classic --no-search --only "$t" --out "$S/fix/regress/$t.jsonl" \
    > "$S/fix/regress/$t.log" 2>&1
  grep -E "alone=" "$S/fix/regress/$t.log"
done
echo "LEMMA TASKS: $(cat "$S/fix/regress/"*.jsonl | grep -c '"automation_alone": true') of $(wc -w < "$S/fix/closed_lemma_he.txt")"
python -u benchmarks/pipeline_check.py --dataset humaneval classic --out "$S/fix/regress/pipeline_he.jsonl" \
  > "$S/fix/regress/pipeline_he.log" 2>&1
echo "PIPELINE: $(grep -c '"outcome": "SOLVED"' "$S/fix/regress/pipeline_he.jsonl") SOLVED of $(wc -l < "$S/fix/regress/pipeline_he.jsonl")"
