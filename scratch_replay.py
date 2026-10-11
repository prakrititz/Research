import sys, json, glob, os, argparse
sys.path.insert(0, '.')
from benchmarks import replay
from benchmarks.cases import CASES
cases = {c["id"]: c for c in CASES}
f = glob.glob(sys.argv[1])[0]
rows = [json.loads(l) for l in open(f, encoding="utf8")]
bad = [r for r in rows if r["outcome"] != "SUCCESS"]
row = bad[int(sys.argv[2])]
os.environ["FORMALLLM_STRICT_VARIANT"] = "0"
args = argparse.Namespace(assist=True, turns=2, max_retries=4, max_depth=6, certify=None)

from FormalLLM.agent import assist
import time
orig=assist.LeafSolver.__init__
def patched(self,*a,**k):
    k['pair_seconds']=float(sys.argv[3]); orig(self,*a,**k)
assist.LeafSolver.__init__=patched
t=time.time()
print(replay.replay_row(row, cases, args)[:2], round(time.time()-t,1))
