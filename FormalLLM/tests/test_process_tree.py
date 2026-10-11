"""A prover that times out must not leave its children running."""
import os
import subprocess
import sys
import time

import pytest

from FormalLLM.verification.backends.process import run_tree

CHILD = "import time; time.sleep(120)"
PARENT = (
    "import subprocess, sys, time\n"
    f"child = subprocess.Popen([sys.executable, '-c', {CHILD!r}])\n"
    "print(child.pid, flush=True)\n"
    "time.sleep(120)\n"
)


def alive(pid: int) -> bool:
    if os.name == "nt":
        out = subprocess.run(["tasklist", "/FI", f"PID eq {pid}", "/NH"], capture_output=True, text=True).stdout
        return str(pid) in out
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def test_a_timeout_kills_the_child_of_the_child(tmp_path):
    script = tmp_path / "parent.py"
    script.write_text(PARENT)
    pid_file = tmp_path / "pid.txt"
    # The parent prints its child's pid, but a timed-out run raises before returning output,
    # so record it through a wrapper that tees stdout to a file.
    wrapper = tmp_path / "wrapper.py"
    wrapper.write_text(
        "import subprocess, sys\n"
        f"p = subprocess.Popen([sys.executable, {str(script)!r}], stdout=subprocess.PIPE, text=True)\n"
        f"open({str(pid_file)!r}, 'w').write(p.stdout.readline())\n"
        "p.wait()\n")
    with pytest.raises(subprocess.TimeoutExpired):
        run_tree([sys.executable, str(wrapper)], cwd=str(tmp_path), timeout=3)
    time.sleep(1.0)
    grandchild = int(pid_file.read_text().strip())
    assert not alive(grandchild), "the grandchild survived the timeout"


def test_a_normal_run_returns_its_output(tmp_path):
    done = run_tree([sys.executable, "-c", "print('hello')"], cwd=str(tmp_path), timeout=30)
    assert done.returncode == 0 and done.stdout.strip() == "hello"


def test_a_failing_run_reports_its_exit_code(tmp_path):
    done = run_tree([sys.executable, "-c", "import sys; sys.exit(3)"], cwd=str(tmp_path), timeout=30)
    assert done.returncode == 3
