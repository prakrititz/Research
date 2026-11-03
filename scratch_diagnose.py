"""Deep diagnostic of why the refinement agent is only solving 54% — analyze every failure."""
import json, os, sys, collections
sys.stdout.reconfigure(encoding='utf-8')

rc2 = r'C:\Users\Prakrititz Borah\AppData\Local\Temp\claude\C--Users-Prakrititz-Borah-Downloads-Work-Research\b020564e-3578-4f9b-a07c-f4f95164f4ca\scratchpad\rc2'
path = os.path.join(rc2, 'benchmarks', 'results', 'lean_agent', 'full_lean_specs_o3-mini.jsonl')
rows = [json.loads(l) for l in open(path, encoding='utf8') if l.strip()]

solved = [r for r in rows if r['outcome'] == 'SOLVED']
exhausted = [r for r in rows if r['outcome'] == 'EXHAUSTED']

print(f"TOTAL: {len(rows)} tasks  |  SOLVED: {len(solved)} ({len(solved)/len(rows)*100:.1f}%)  |  EXHAUSTED: {len(exhausted)} ({len(exhausted)/len(rows)*100:.1f}%)")
print()

# --- 1. How many calls before giving up? ---
print("=== 1. BUDGET / CALLS ANALYSIS ===")
for r in exhausted[:5]:
    print(f"  {r['task']}: {r['calls']} calls, {r['retractions']} retractions, detail: {r['detail']}")
calls_dist = collections.Counter(r['calls'] for r in exhausted)
print(f"  Exhausted calls distribution: {dict(sorted(calls_dist.items()))}")
print()

# --- 2. What are the failure reasons? ---
print("=== 2. FAILURE TAXONOMY (from call_outcomes of exhausted tasks) ===")
outcome_counts = collections.Counter()
for r in exhausted:
    for o in r.get('call_outcomes', []):
        outcome_counts[o] += 1
for k, v in outcome_counts.most_common():
    print(f"  {k}: {v}")
print()

# --- 3. What feedback patterns dominate? ---
print("=== 3. TOP FEEDBACK PATTERNS (what Lean tells the model) ===")
feedback_patterns = collections.Counter()
for r in exhausted:
    for fb in r.get('feedback', []):
        # Extract the key phrase
        if 'ill formed' in fb:
            feedback_patterns['ill_formed'] += 1
        elif 'unproved' in fb:
            feedback_patterns['unproved'] += 1
        elif 'timeout' in fb or 'heartbeats' in fb:
            feedback_patterns['timeout/heartbeats'] += 1
        elif 'not accepted' in fb:
            feedback_patterns['not_accepted'] += 1
        elif 'state variables' in fb:
            feedback_patterns['wrong_init_count'] += 1
        elif 'Unknown' in fb or 'unknown' in fb:
            feedback_patterns['unknown_identifier'] += 1
        else:
            feedback_patterns['other'] += 1
for k, v in feedback_patterns.most_common():
    print(f"  {k}: {v}")
print()

# --- 4. Detailed look at feedback for EXHAUSTED tasks ---
print("=== 4. SAMPLE EXHAUSTED TASKS — FIRST FEEDBACK ===")
for r in exhausted[:15]:
    fb_list = r.get('feedback', [])
    first_fb = fb_list[0][:200] if fb_list else '(no feedback)'
    print(f"  {r['task']} ({r['calls']} calls): {first_fb}")
print()

# --- 5. How many tasks had Lean syntax errors vs proof failures? ---
print("=== 5. ILL-FORMED vs UNPROVED breakdown ===")
ill_formed_tasks = 0
unproved_tasks = 0
mixed_tasks = 0
for r in exhausted:
    outcomes = set(r.get('call_outcomes', []))
    has_ill = 'ill_formed' in outcomes
    has_unproved = 'unproved' in outcomes or 'lemma_unproved' in outcomes
    if has_ill and has_unproved:
        mixed_tasks += 1
    elif has_ill:
        ill_formed_tasks += 1
    elif has_unproved:
        unproved_tasks += 1
print(f"  Pure ill-formed (syntax/API errors): {ill_formed_tasks}")
print(f"  Pure unproved (valid syntax, proof obligation failed): {unproved_tasks}")
print(f"  Mixed (both): {mixed_tasks}")
print()

# --- 6. Were any tasks solved by the hand-written oracle but NOT by the agent? ---
oracle_path = os.path.join(rc2, 'benchmarks', 'results', 'lean_specs', 'oracle.json')
if os.path.exists(oracle_path):
    oracles = json.load(open(oracle_path, encoding='utf8'))
    oracle_ids = {o['id'] for o in oracles if o.get('certified')}
    agent_solved = {r['task'] for r in solved}
    missed = oracle_ids - agent_solved
    print(f"=== 6. ORACLE-CERTIFIED but AGENT FAILED ({len(missed)} tasks) ===")
    for m in sorted(missed):
        match = [r for r in exhausted if r['task'] == m]
        if match:
            r = match[0]
            print(f"  {m}: {r['calls']} calls, outcomes: {r['call_outcomes'][:5]}")
    print()

# --- 7. Solved task call distribution ---
print("=== 7. SOLVED TASKS — calls needed ===")
solved_calls = collections.Counter(r['calls'] for r in solved)
for k in sorted(solved_calls):
    print(f"  {k} calls: {solved_calls[k]} tasks")
print()

# --- 8. Config check ---
print("=== 8. CONFIG CHECK ===")
if rows:
    r0 = rows[0]
    print(f"  config: {r0.get('config')}")
    # Check the agent parameters from the detail field
    print(f"  Sample task detail: {r0.get('detail', '(none)')}")
    print(f"  Max calls in any exhausted: {max(r['calls'] for r in exhausted) if exhausted else 0}")
    print(f"  Typical exhausted calls: {sum(r['calls'] for r in exhausted) / len(exhausted):.1f}")
