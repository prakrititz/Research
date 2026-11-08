"""A managed Lean 4 session: one process, Mathlib imported once, a timeout on every command.

Starting ``lake env lean`` per obligation re-imports Mathlib each time (about 12 s warm). The Lean REPL
(``leanprover-community/repl``, built under ``~/.formalllm/repl``) imports once and then checks each command
against the kept environment: 12 s once, then about 0.2 s per obligation (``Reading Material/22``). A tactic that
never returns would block the shared process, so every command runs under a wall-clock limit; on a timeout the process
is killed and restarted (the import is paid again) and the reply says ``timed_out``.

    with LeanSession() as lean:
        reply = lean.run("theorem t (a : Int) (h : a > 0) : a + 1 > 1 := by omega")
        assert reply.ok

``LeanReply`` keeps what a refiner needs: error texts (the first line is the headline, the rest is the goal state Lean
prints for ``linarith``/``omega`` failures), warnings, ``#eval`` output, and the goals of any ``sorry``.
"""
import json
import os
import subprocess
import threading
import time
from dataclasses import dataclass, field
from typing import List, Optional

HOME = os.path.join(os.path.expanduser("~"), ".formalllm")


# --- where Lean lives (self-contained: nothing here depends on the earlier Z3-era ``FormalLLM/verification`` package) --------

def short_path(path: str) -> str:
    """Windows 8.3 form of ``path`` (no spaces), which Lake and Lean handle more reliably; unchanged elsewhere."""
    if os.name != "nt" or not os.path.exists(path):
        return path
    try:
        import ctypes
        buf = ctypes.create_unicode_buffer(32768)
        if ctypes.windll.kernel32.GetShortPathNameW(path, buf, len(buf)):
            return buf.value
    except Exception:
        pass
    return path


@dataclass
class Toolchain:
    """``elan`` in ``~/.formalllm/elan`` and a Lake project requiring Mathlib in ``~/.formalllm/lean-env-parent/lean-env``
    (override with ``FORMALLLM_ELAN_HOME`` / ``FORMALLLM_LEAN_PROJECT``; the REPL with ``FORMALLLM_LEAN_REPL``)."""
    elan_home: str = field(default_factory=lambda: os.environ.get("FORMALLLM_ELAN_HOME") or os.path.join(HOME, "elan"))
    project: str = field(default_factory=lambda: os.environ.get("FORMALLLM_LEAN_PROJECT")
                         or os.path.join(HOME, "lean-env-parent", "lean-env"))
    repl: str = field(default_factory=lambda: os.environ.get("FORMALLLM_LEAN_REPL") or os.path.join(
        HOME, "repl", ".lake", "build", "bin", "repl.exe" if os.name == "nt" else "repl"))

    @property
    def lake(self) -> str:
        return os.path.join(self.elan_home, "bin", "lake.exe" if os.name == "nt" else "lake")

    @property
    def available(self) -> bool:
        return os.path.exists(self.lake) and os.path.isdir(self.project) and os.path.exists(self.repl)

    def env(self) -> dict:
        env = dict(os.environ)
        env["ELAN_HOME"] = short_path(self.elan_home)
        env["PATH"] = short_path(os.path.join(self.elan_home, "bin")) + os.pathsep + env.get("PATH", "")
        return env

    def command(self, *tail: str) -> list:
        """``lake env <tail>`` inside the project (run it with ``cwd=short_path(project)`` and ``env=self.env()``)."""
        return [self.lake, "env", *tail]

    def spawn_repl(self) -> subprocess.Popen:
        if not self.available:
            raise LeanUnavailable(f"Lean project ({self.project}), lake ({self.lake}) or the REPL ({self.repl}) is missing; "
                                  "see Reading Material/22")
        return subprocess.Popen(self.command(self.repl), cwd=short_path(self.project), env=self.env(),
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                text=True, encoding="utf8", bufsize=1)


#: Small imports that cover the arithmetic, list and counter-example tactics the refinement obligations use.
DEFAULT_IMPORTS = ("import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Positivity\n"
                   "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Ring\nimport Mathlib.Data.List.Basic\nimport Mathlib.Data.List.Sort\n"
                   "import Mathlib.Data.Nat.Prime.Basic\nimport Plausible")
#: ``FORMALLLM_LEAN_IMPORTS`` swaps in another header, e.g. ``import LeanEnv.Hammer`` with the hammer project as
#: ``FORMALLLM_LEAN_PROJECT`` (Mathlib + Duper + lean-auto + Zipperposition, ``refine_hammer``)
FULL_IMPORTS = os.environ.get("FORMALLLM_LEAN_IMPORTS", "import Mathlib")


class LeanUnavailable(RuntimeError):
    """Lean, the project or the REPL is not installed where it is expected."""


@dataclass
class LeanReply:
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    infos: List[str] = field(default_factory=list)
    goals: List[str] = field(default_factory=list)          # one per ``sorry``
    seconds: float = 0.0
    timed_out: bool = False
    error_lines: List[int] = field(default_factory=list)    # the line of each error, in the order of ``errors``
    info_lines: List[int] = field(default_factory=list)     # the line of each info, in the order of ``infos``

    @property
    def ok(self) -> bool:
        """No error, no timeout and no ``sorry`` (a theorem that is really proved)."""
        return not self.errors and not self.goals and not self.timed_out

    @property
    def headline(self) -> str:
        if self.timed_out:
            return "Lean gave no answer within the time limit"
        if self.errors:
            return self.errors[0].splitlines()[0][:200]
        return "declaration uses sorry" if self.goals else ""

    @property
    def counterexample(self) -> Optional[str]:
        """The values ``plausible`` reports, e.g. ``a := 1, b := 0``, or ``None``."""
        for text in self.errors:
            if "Found a counter-example" in text:
                lines = [l for l in text.split("counter-example!", 1)[1].splitlines() if ":=" in l]
                return ", ".join(l.strip() for l in lines) or None
        return None


class LeanSession:
    def __init__(self, imports: str = DEFAULT_IMPORTS, command_timeout: float = 120.0, startup_timeout: float = 900.0):
        self.imports = imports
        self.command_timeout = command_timeout
        self.startup_timeout = startup_timeout
        self.process: Optional[subprocess.Popen] = None
        self.env: Optional[int] = None
        self.startup_seconds = 0.0
        self.restarts = 0
        self._start()

    # --- process management ---------------------------------------------------------------------------------------

    def _start(self, attempts: int = 3):
        """Spawn the REPL and import. A starved machine can refuse a new process for a while (Windows: "fork: Resource
        temporarily unavailable"), so try a few times, cleaning up the half-started process tree in between."""
        for attempt in range(attempts):
            self.process = Toolchain().spawn_repl()
            started = time.time()
            reply = self._exchange({"cmd": self.imports}, self.startup_timeout)
            if reply is not None:
                self.env = reply["env"]
                self.startup_seconds = time.time() - started
                return
            self.close()
            if attempt + 1 < attempts:
                time.sleep(15 * (attempt + 1))
        raise LeanUnavailable(f"the Lean REPL did not finish importing ({attempts} attempts)")

    def _exchange(self, message: dict, timeout: float):
        """Send one JSON command and read one JSON reply; ``None`` if nothing came back in ``timeout`` seconds."""
        box = {}

        def work():
            try:
                # raw UTF-8, not \uXXXX escapes: the REPL's JSON reader turns a surrogate pair (any character outside the
                # basic plane, e.g. an emoji) into two invalid characters
                self.process.stdin.write(json.dumps(message, ensure_ascii=False) + "\n\n")
                self.process.stdin.flush()
                text = ""
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        box["error"] = "the Lean REPL ended"
                        return
                    if line.strip() == "" and text.strip():
                        break
                    text += line
                box["reply"] = json.loads(text)
            except Exception as error:                       # a broken pipe, bad JSON
                box["error"] = str(error)
        thread = threading.Thread(target=work, daemon=True)
        thread.start()
        thread.join(timeout)
        return None if thread.is_alive() or "error" in box else box["reply"]

    def close(self):
        process, self.process = self.process, None
        if process is None:
            return
        try:                                   # the REPL runs as a grandchild (lake -> lake -> repl): remember the whole tree
            import psutil
            tree = psutil.Process(process.pid).children(recursive=True)
        except Exception:
            tree = []
        try:
            process.stdin.close()
            process.wait(timeout=5)
        except Exception:
            process.kill()
        # on Windows the children outlive their parent: without this every restart leaked a full REPL (GBs)
        for child in tree:
            try:
                child.kill()
            except Exception:
                pass

    def restart(self):
        self.close()
        self.restarts += 1
        self._start()

    def memory_gb(self) -> float:
        """Resident memory of the REPL and its children. It only grows: every task's environment stays in the REPL."""
        try:
            import psutil
            root = psutil.Process(self.process.pid)
            return sum(p.memory_info().rss for p in [root, *root.children(recursive=True)]) / 2 ** 30
        except Exception:
            return 0.0

    def recycle(self, limit_gb: Optional[float] = None) -> bool:
        """Restart the REPL when it holds more than ``limit_gb`` (default ``FORMALLLM_LEAN_MAX_GB``, 6 GB; a fresh REPL with
        Mathlib holds about 3.6 GB). Call between tasks: a long run otherwise starves the machine and later tasks time out
        (found 2026-10-26: two REPLs at 5.5 and 4.1 GB after ~100 tasks each, 2.8 GB left free)."""
        limit = limit_gb if limit_gb is not None else float(os.environ.get("FORMALLLM_LEAN_MAX_GB", "6"))
        if self.process is not None and self.memory_gb() > limit:
            self.restart()
            return True
        return False

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    # --- commands -------------------------------------------------------------------------------------------------

    def run(self, command: str, timeout: Optional[float] = None, env: Optional[int] = None) -> LeanReply:
        """Elaborate ``command`` in the imported environment, or in ``env`` (from :meth:`load`); declarations of this
        command do not persist."""
        reply, _ = self._run(command, timeout, self.env if env is None else env)
        return reply

    def load(self, command: str, timeout: Optional[float] = None,
             env: Optional[int] = None) -> "tuple[LeanReply, Optional[int]]":
        """Elaborate ``command`` and keep what it declares: returns the reply and the id of the extended environment
        (``None`` if it failed), on top of ``env`` (default: the imports). Environment ids are void after a restart
        (compare :attr:`restarts`)."""
        reply, new_env = self._run(command, timeout, self.env if env is None else env)
        return reply, (None if reply.errors or reply.timed_out else new_env)

    def library_env(self, library: str, timeout: float = 1200.0) -> Optional[int]:
        """The environment with ``library`` (the engine's lemma library, ~140k characters) elaborated, once per process
        (again after a restart). Every task builds on it: re-elaborating the library for each task's environment and
        twice more for its certificate took ~80 s each time (2026-11-08: he_002 spent 246 s in Lean, 0.2 s of it on
        its one obligation). ``None`` if it does not load (the caller then falls back to sending the text)."""
        cache = self.__dict__.setdefault("_libraries", {})
        key = (hash(library), self.restarts)
        if key not in cache:
            env = self._library_from_module(library, timeout)
            if env is None:
                reply, env = self.load(library, timeout=timeout)
            if env is None:
                return None
            cache[key] = env
        return cache[key]

    def _library_from_module(self, library: str, timeout: float) -> Optional[int]:
        """The library imported from its compiled module (``library_module.py``) instead of elaborated: the REPL is
        restarted every few tasks to bound its memory, and re-elaborating the library took ~37 s each time (Mac,
        2026-11-08). ``None`` when the module cannot be built or imported (the text is elaborated as before)."""
        if os.environ.get("FORMALLLM_LIBRARY_MODULE", "1") == "0" or self.imports.strip() != FULL_IMPORTS.strip():
            return None                     # the module imports FULL_IMPORTS: only for a session with exactly those
        try:
            from FormalLLM.lean.library_module import ensure
            module = ensure(library)
        except Exception:
            return None
        if module is None:
            return None
        reply, env = self._run(f"{self.imports}\nimport {module}", timeout, None)
        return None if reply.errors or reply.timed_out else env

    def _run(self, command: str, timeout: Optional[float], env: Optional[int]):
        started = time.time()
        raw = self._exchange({"cmd": command, "env": env}, timeout or self.command_timeout)
        if raw is None:
            self.restart()
            return LeanReply(errors=["timeout"], seconds=time.time() - started, timed_out=True), None
        reply = LeanReply(seconds=time.time() - started)
        for message in raw.get("messages", []):
            severity = message.get("severity")
            bucket = {"error": reply.errors, "warning": reply.warnings, "info": reply.infos}.get(severity)
            if bucket is not None:
                bucket.append(message.get("data", ""))
                line = (message.get("pos") or {}).get("line", 0)
                if severity == "error":
                    reply.error_lines.append(line)
                elif severity == "info":
                    reply.info_lines.append(line)
        reply.goals = [s.get("goal", "") for s in (raw.get("sorries") or [])]
        return reply, raw.get("env")
