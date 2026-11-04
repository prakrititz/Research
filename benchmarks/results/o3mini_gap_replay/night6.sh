#!/bin/bash
# HumanEval gap replay, then the lemma-task regression, then the Verina gap replay (gb6_*)
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
replay() {
  for round in $(seq 1 30); do
    # a fresh process every 4 trials (Lean memory does not pile up)
    python -u "$S/fix/gate_b.py" "$S/rc2" "benchmarks/results/lean_agent/full_$1_o3-mini.jsonl" "$S/fix/gb6_$1.jsonl" \
      --limit 4 --only $(cat "$S/fix/gap6_$1.txt") > "$S/fix/gb_round.log" 2>&1
    cat "$S/fix/gb_round.log" >> "$S/fix/gb6_$1.log"
    left=$(head -1 "$S/fix/gb_round.log" | awk '{print $1}')
    [ "$left" = "0" ] && break
  done
  echo "GATE B $1 done"
}
replay lean_specs
mkdir -p "$S/fix/regress6"
for t in $(cat "$S/fix/closed_lemma_he.txt"); do
  [ -s "$S/fix/regress6/$t.jsonl" ] && continue
  python -u benchmarks/prover_ceiling.py --dataset humaneval classic --no-search --only "$t" --out "$S/fix/regress6/$t.jsonl" \
    > "$S/fix/regress6/$t.log" 2>&1
  echo "$t $(grep -oE 'alone=[A-Za-z]+' "$S/fix/regress6/$t.log" | head -1)"
done
echo "LEMMA TASKS: $(cat "$S/fix/regress6/"*.jsonl | grep -c '"automation_alone": true') of $(wc -w < "$S/fix/closed_lemma_he.txt")"
replay verina
echo NIGHT6 DONE
