import sys, json, os, io, contextlib, argparse
sys.path.insert(0, '.')
from benchmarks import replay
from benchmarks.cases import CASES
cases = {c["id"]: c for c in CASES}
rows = [json.loads(l) for l in open('benchmarks/results/datasets/he_refine_v7.jsonl', encoding='utf8') if l.strip()]
row = [r for r in rows if r['task_id']=='HumanEval/13' and r['repeat']==0][0]
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
args = argparse.Namespace(assist=True, turns=2, max_retries=4, max_depth=6, certify=None)
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    out = replay.replay_row(row, cases, args)
print(out)
print(buf.getvalue()[-3000:])
