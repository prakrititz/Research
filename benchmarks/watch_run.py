"""Watchdog for one paid run: python watch_run.py <log> <results.jsonl> <script name>.
Prints one line per finished task; kills the run when too many tasks fail; exits when the run's process is gone."""
import json, os, subprocess, sys, time

LOG, OUT, SCRIPT = sys.argv[1], sys.argv[2], sys.argv[3]
FAIL = {"EXHAUSTED", "ERROR", "UNVERIFIED"}


def rows():
    out = []
    if os.path.exists(OUT):
        for line in open(OUT, encoding="utf8"):
            try:
                out.append(json.loads(line))
            except ValueError:
                pass
    return out


def run_pids():
    ps = ("Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -like '*" + SCRIPT + "*' -and "
          "$_.Name -like 'python*' -and $_.CommandLine -notlike '*watch_run*' } | ForEach-Object { $_.ProcessId }")
    done = subprocess.run(["powershell", "-NoProfile", "-Command", ps], capture_output=True, text=True)
    return [p.strip() for p in done.stdout.split() if p.strip().isdigit()]


def spent():
    last = "?"
    try:
        for line in open(LOG, encoding="utf8", errors="replace"):
            if line.startswith("[Usage:"):
                last = line.split("Cumulative Total:")[1].split("/")[0].strip()
    except OSError:
        pass
    return last


seen = len(rows())          # rows from an earlier run of the same file are not this run's
start_rows = seen
time.sleep(30)              # let the run's process start
while True:
    rs = rows()
    for r in rs[seen:]:
        print(f"{r.get('id') or r.get('task')} {r['outcome']} calls={r.get('calls')} spent={spent()}", flush=True)
    seen = len(rs)
    outcomes = [r["outcome"] for r in rs[start_rows:]]
    n, fails = len(outcomes), sum(o in FAIL for o in outcomes)
    reason = None
    if n >= 10 and fails / n > 0.7:
        reason = f"{fails}/{n} tasks failed (>70%)"
    elif n >= 6 and all(o in FAIL for o in outcomes[-6:]):
        reason = "6 failures in a row"
    elif n >= 3 and all(o == "ERROR" for o in outcomes[-3:]):
        reason = "3 errors in a row"
    pids = run_pids()
    if reason and pids:
        for pid in pids:
            subprocess.run(["taskkill", "/PID", pid, "/T", "/F"], capture_output=True)
        print(f"WATCHDOG STOPPED THE RUN: {reason}; spent {spent()}", flush=True)
        break
    if not pids:
        print(f"RUN ENDED: {n} rows, {fails} failed; spent {spent()}", flush=True)
        break
    time.sleep(60)
