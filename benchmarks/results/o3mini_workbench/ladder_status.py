import json, os, re, sys
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
S = os.path.dirname(os.path.abspath(__file__))
dev = open(os.path.join(S, "dev_tasks.txt")).read().split()
names = {"R0": "old code", "R1": "+fix1 engine/budget", "R2": "+fix2 Lean grounding", "R3": "+fix3 name hints",
         "R4": "+fix4 worked examples", "R5": "+fix5 proof sub-agent"}
for r, label in names.items():
    tree = "ctrl" if r == "R0" else "rc2"
    p = os.path.join(S, tree, "benchmarks", "results", "lean_agent", f"ladder_{r}.jsonl")
    rows = [json.loads(l) for l in open(p, encoding="utf8")] if os.path.exists(p) else []
    log = open(os.path.join(S, "ladder", f"{r}.log"), encoding="utf8", errors="replace").read() if os.path.exists(os.path.join(S, "ladder", f"{r}.log")) else ""
    cost = re.findall(r"Cumulative Total: \$([0-9.]+)", log)
    solved = [x["task"] for x in rows if x["verified"]]
    print(f"{r} {label:24s} {len(rows):2d}/16 done  solved {len(solved):2d}  calls {sum(x['calls'] for x in rows):3d}  "
          f"cost ${cost[-1] if cost else '0'}  http_err {len(re.findall('returned HTTP', log))}  tb {log.count('Traceback')}")
    if "-v" in sys.argv and solved:
        print("     solved:", " ".join(solved))
