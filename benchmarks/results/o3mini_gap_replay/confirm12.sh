#!/bin/bash
# Re-certify the 12 newly fixed tasks, each in its own fresh process (keeps Lean memory from piling up).
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
mkdir -p "$S/fix/confirm"
for t in he_090_next_smallest he_136_largest_smallest_integers he_145_order_by_points he_114_min_sub_array_sum classic_fast_power \
         he_038_decode_cyclic he_033_sort_third he_037_sort_even he_044_change_base he_025_factorize he_020_find_closest_elements \
         he_001_separate_paren_groups; do
  [ -s "$S/fix/confirm/$t.jsonl" ] && continue
  python -u benchmarks/prover_ceiling.py --dataset humaneval classic --no-search --only "$t" --out "$S/fix/confirm/$t.jsonl" \
    > "$S/fix/confirm/$t.log" 2>&1
  grep -E "alone=" "$S/fix/confirm/$t.log"
done
echo DONE
cat "$S/fix/confirm/"*.jsonl | grep -c '"automation_alone": true'
