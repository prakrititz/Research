"""Run a prover as a child process that dies *with all its children* when it times out.

``subprocess.run(..., timeout=T)`` kills only the process it started. ``coqc`` hands proof
checking to ``rocqworker`` and ``lake`` starts ``lean``; killing the parent leaves them running
at full CPU. Measured: after a handful of timed-out proof searches, six orphaned
``rocqworker.exe`` processes were still burning cores half an hour later. A prover is allowed to
fail, never to leak, so every timeout kills the whole tree.
"""
import os
import signal
import subprocess
from typing import Dict, List, Optional


def kill_tree(process: subprocess.Popen) -> None:
    """Terminate ``process`` and every descendant."""
    if os.name == "nt":
        subprocess.run(["taskkill", "/F", "/T", "/PID", str(process.pid)], capture_output=True)
    else:
        try:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            process.kill()


def run_tree(command: List[str], cwd: str, timeout: float, env: Optional[Dict[str, str]] = None,
             encoding: Optional[str] = None) -> subprocess.CompletedProcess:
    """Like ``subprocess.run(capture_output=True, text=True)`` but a timeout kills the whole tree."""
    kwargs = {"cwd": cwd, "stdout": subprocess.PIPE, "stderr": subprocess.PIPE, "text": True, "env": env}
    if encoding:
        kwargs["encoding"] = encoding
    if os.name == "nt":
        kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        kwargs["start_new_session"] = True
    process = subprocess.Popen(command, **kwargs)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        kill_tree(process)
        process.communicate()
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
