#!/bin/bash
# Unattended, after the cascade fix (889d8a9): the 25 lemma tasks (prover alone), gate B on the HumanEval trials, the full
# HumanEval + classics pipeline, gate B on the Verina trials. One Lean process at a time; every step resumable.
S="C:/Users/PRAKRI~1/AppData/Local/Temp/claude/C--Users-Prakrititz-Borah-Downloads-Work-Research/b020564e-3578-4f9b-a07c-f4f95164f4ca/scratchpad"
R="$S/fix/regress2"
cd "$S/rc2" || exit 1
export FORMALLLM_LEAN_PROJECT="$HOME/.formalllm/lean-env-parent/lean-env-hammer" FORMALLLM_LEAN_IMPORTS="import LeanEnv.Hammer" PYTHONIOENCODING=utf-8
mkdir -p "$R"
for t in $(cat "$S/fix/closed_lemma_he.txt"); do
  [ -s "$R/$t.jsonl" ] && continue
  python -u benchmarks/prover_ceiling.py --dataset humaneval classic --no-search --only "$t" --out "$R/$t.jsonl" > "$R/$t.log" 2>&1
  grep -E "alone=" "$R/$t.log"
done
echo "LEMMA TASKS: $(cat "$R/"*.jsonl | grep -c '"automation_alone": true') of $(wc -w < "$S/fix/closed_lemma_he.txt")"
gate_b() {
  for round in $(seq 1 30); do
    # a fresh process every 8 trials (Lean memory does not pile up)
    python -u "$S/fix/gate_b.py" "$S/rc2" "benchmarks/results/lean_agent/full_$1_o3-mini.jsonl" "$S/fix/gb_$1.jsonl" \
      --limit 8 > "$S/fix/gb_round.log" 2>&1
    cat "$S/fix/gb_round.log" >> "$S/fix/gb_$1.log"
    left=$(head -1 "$S/fix/gb_round.log" | awk '{print $1}')
    [ "$left" = "0" ] && break
  done
  echo "GATE B $1: $(wc -l < "$S/fix/gb_$1.jsonl") trials replayed"
}
gate_b lean_specs
python -u benchmarks/pipeline_check.py --dataset humaneval classic --out "$R/pipeline_he.jsonl" > "$R/pipeline_he.log" 2>&1
echo "PIPELINE: $(grep -c '"outcome": "SOLVED"' "$R/pipeline_he.jsonl") SOLVED of $(wc -l < "$R/pipeline_he.jsonl")"
gate_b verina
echo NIGHT2 DONE
