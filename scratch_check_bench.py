import json
import os
import sys

sys.stdout.reconfigure(encoding='utf-8')
rc2 = r'C:\Users\Prakrititz Borah\AppData\Local\Temp\claude\C--Users-Prakrititz-Borah-Downloads-Work-Research\b020564e-3578-4f9b-a07c-f4f95164f4ca\scratchpad\rc2'
res_dir = os.path.join(rc2, 'benchmarks', 'results', 'lean_agent')

def analyze(filename, total_expected):
    path = os.path.join(res_dir, filename)
    if not os.path.exists(path):
        print(f"File not found: {path}")
        return
    lines = [json.loads(l) for l in open(path, encoding='utf8') if l.strip()]
    solved = [l for l in lines if l.get('outcome') == 'SOLVED']
    exhausted = [l for l in lines if l.get('outcome') == 'EXHAUSTED']
    verified = [l for l in lines if l.get('verified') is True]
    total_time = sum(l.get('seconds', 0) for l in lines)
    total_calls = sum(l.get('calls', 0) for l in lines)
    print(f"=== {filename} ===")
    print(f"Progress: {len(lines)} / {total_expected} tasks completed ({len(lines)/total_expected*100:.1f}%)")
    print(f"Solved & Verified: {len(solved)} / {len(lines)} ({len(solved)/len(lines)*100:.1f}%)")
    print(f"Exhausted: {len(exhausted)} / {len(lines)} ({len(exhausted)/len(lines)*100:.1f}%)")
    print(f"Total LLM calls: {total_calls}")
    print(f"Total benchmark time so far: {total_time/60:.1f} minutes")
    if lines:
        last = lines[-1]
        print(f"Last completed task: {last['task']} -> {last['outcome']} (calls: {last.get('calls')}, time: {last.get('seconds', 0)}s)")
        print(f"Recent 5 completed:")
        for t in lines[-5:]:
            print(f"  * {t['task']}: {t['outcome']} (calls: {t.get('calls')}, verified: {t.get('verified')})")
    print()

analyze('full_lean_specs_o3-mini.jsonl', 169)
analyze('full_verina_o3-mini.jsonl', 189)
