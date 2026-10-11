import sys, json, glob, os, argparse, io, contextlib
sys.path.insert(0, '.')
from benchmarks import replay
from benchmarks.cases import CASES
cases = {c["id"]: c for c in CASES}
f = glob.glob("benchmarks/results/reliability/v6_relaxed_assist_*.jsonl")[0]
rows = [json.loads(l) for l in open(f, encoding="utf8")]
row = [r for r in rows if r["outcome"] == "SUCCESS" and r["llm_calls"] == 2][0]
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
args = argparse.Namespace(assist=True, turns=2, max_retries=4, max_depth=6, certify=["coq"])
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    outcome, calls, program, cert = replay.replay_row(row, cases, args)
print("RAW REPLIES:")
for r in row["raw_responses"]: print(r)
print("NARRATION:"); print(buf.getvalue()[-6000:])
print("OUTCOME", outcome, calls); print(program); print(json.dumps(cert, indent=1)[:1500])
