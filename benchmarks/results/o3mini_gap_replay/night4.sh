#!/bin/bash
# lemma-task regression (prover alone), then the replay of every task with an open step
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
mkdir -p "$S/fix/regress4"
for t in $(cat "$S/fix/closed_lemma_he.txt"); do
  [ -s "$S/fix/regress4/$t.jsonl" ] && continue
  python -u benchmarks/prover_ceiling.py --dataset humaneval classic --no-search --only "$t" --out "$S/fix/regress4/$t.jsonl" \
    > "$S/fix/regress4/$t.log" 2>&1
  echo "$t $(grep -oE 'alone=[A-Za-z]+' "$S/fix/regress4/$t.log" | head -1)"
done
echo "LEMMA TASKS: $(cat "$S/fix/regress4/"*.jsonl | grep -c '"automation_alone": true') of $(wc -w < "$S/fix/closed_lemma_he.txt")"
bash "$S/fix/gaps4.sh"
