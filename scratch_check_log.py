import sys
import re

sys.stdout.reconfigure(encoding='utf-8')
log_path = r'C:\Users\Prakrititz Borah\.gemini\antigravity-ide\brain\3bfbe0dc-546a-4553-98b5-a43e423ae462\.system_generated\tasks\task-725.log'
content = open(log_path, encoding='utf8', errors='ignore').read()

tasks = re.findall(r'Task:\s*(\w+)', content)
print('Number of task occurrences:', len(tasks))
seen = []
for t in tasks:
    if t not in seen:
        seen.append(t)
print('Tasks attempted in order:', seen)
usages = re.findall(r'Cumulative Total:\s*\$([0-9.]+)', content)
if usages:
    print('Last recorded spend: $' + usages[-1])
