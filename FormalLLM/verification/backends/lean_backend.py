"""Certify proof obligations with Lean 4 and Mathlib.

Each obligation becomes a theorem (see :mod:`lspec.lean_translator`) closed by a
cascade of arithmetic tactics and checked by ``lean``. Acceptance means Lean's
kernel checked the proof term. As with Coq, failing to find a proof refutes
nothing, so that case is UNKNOWN, never FAILED.

Cost: every run imports Mathlib (about 8 s on this machine), so Lean is meant
for *certifying* a finished derivation, not for the inner search loop; results
are cached by a hash of the generated source.

Installation (user level, no admin): ``elan`` in ``~/.formalllm/elan`` and a
Lake project with Mathlib in ``~/.formalllm/lean-env-parent/lean-env``.
Override with ``FORMALLLM_LEAN_PROJECT`` / ``FORMALLLM_ELAN_HOME``.
"""

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from typing import Dict, List, Optional, Tuple

from FormalLLM.lspec.coq_translator import UnsupportedForBackend
from FormalLLM.lspec.lean_translator import obligation_to_lean
from FormalLLM.verification.backends.base import VerificationResult
from FormalLLM.verification.backends.process import run_tree

#: Tried in order on every conjunct of the goal. ``omega`` (integers), ``linarith`` /
#: ``nlinarith`` / ``positivity`` (real arithmetic) are fast. ``grind`` is an SMT-style
#: engine -- E-matching for quantified hypotheses, congruence closure for function (array)
#: applications, integer arithmetic -- whose result is still checked by Lean's kernel. It
#: is what lets Lean certify obligations with array axioms and quantifiers (21 of 21 on
#: the classic derivations, where plain arithmetic tactics manage 9).
TACTICS = ("omega", "linarith", "nlinarith", "positivity", "grind")

IMPORTS = ("import Mathlib.Data.Real.Basic\n"
           "import Mathlib.Tactic.Linarith\n"
           "import Mathlib.Tactic.Positivity\n"
           "import Mathlib.Tactic.NormNum\n")


def short_path(path: str) -> str:
    """Windows 8.3 form of ``path`` (no spaces), which Lake and Lean handle more reliably."""
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


def _home() -> str:
    return os.path.join(os.path.expanduser("~"), ".formalllm")


class LeanBackend:
    name = "lean"

    def __init__(self, project: Optional[str] = None, elan_home: Optional[str] = None,
                 timeout_s: float = 240.0, proof_dir: Optional[str] = None):
        self.project = project or os.environ.get("FORMALLLM_LEAN_PROJECT") or \
            os.path.join(_home(), "lean-env-parent", "lean-env")
        self.elan_home = elan_home or os.environ.get("FORMALLLM_ELAN_HOME") or os.path.join(_home(), "elan")
        self.timeout_s = timeout_s
        self.proof_dir = proof_dir or os.environ.get("FORMALLLM_PROOF_DIR")
        self._cache: Dict[str, Tuple[str, str]] = {}
        self._version: Optional[str] = None
        self.stats = {"proved": 0, "unknown": 0, "cached": 0}

    # --- environment ----------------------------------------------------------

    @property
    def lake(self) -> str:
        exe = "lake.exe" if os.name == "nt" else "lake"
        return os.path.join(self.elan_home, "bin", exe)

    @property
    def available(self) -> bool:
        return os.path.exists(self.lake) and os.path.isdir(self.project)

    def _env(self) -> dict:
        env = dict(os.environ)
        env["ELAN_HOME"] = short_path(self.elan_home)
        env["PATH"] = short_path(os.path.join(self.elan_home, "bin")) + os.pathsep + env.get("PATH", "")
        return env

    def version(self) -> str:
        if self._version is None:
            out = subprocess.run([self.lake, "env", "lean", "--version"], cwd=short_path(self.project),
                                 capture_output=True, text=True, timeout=60, env=self._env())
            self._version = (out.stdout or out.stderr).strip().splitlines()[0]
        return self._version

    # --- source ---------------------------------------------------------------

    def theorem_text(self, obligation, name: str = "obl") -> str:
        """The theorem for ``obligation`` and its proof, without imports."""
        header, _sorts, parts = obligation_to_lean(obligation, name=name)
        description = (getattr(obligation, "description", None) or "proof obligation").replace("\n", " ")
        split = ("  refine ⟨" + ", ".join(["?_"] * parts) + "⟩\n") if parts > 1 else ""
        tactics = "\n".join(f"    | {t}" for t in TACTICS)
        return f"-- {description}\n{header}\n{split}  all_goals first\n{tactics}\n"

    def source(self, obligation) -> str:
        return f"{IMPORTS}\n{self.theorem_text(obligation)}"

    # --- verification ---------------------------------------------------------

    def verify(self, obligation, timeout_ms: Optional[int] = None) -> Tuple[str, str]:
        if not self.available:
            return VerificationResult.UNKNOWN, "Lean is not installed (see FORMALLLM_LEAN_PROJECT)"
        try:
            text = self.source(obligation)
        except UnsupportedForBackend as e:
            return VerificationResult.UNKNOWN, f"not translatable to Lean: {e}"

        key = hashlib.sha256(text.encode("utf8")).hexdigest()[:16]
        if key in self._cache:
            self.stats["cached"] += 1
            return self._cache[key]

        timeout = (timeout_ms / 1000.0) if timeout_ms and timeout_ms > 1000 else self.timeout_s
        workdir = tempfile.mkdtemp(prefix="fllm_lean_")
        path = os.path.join(workdir, f"obl_{key}.lean")
        with open(path, "w", encoding="utf8") as fh:
            fh.write(text)
        try:
            done = run_tree([self.lake, "env", "lean", short_path(path)], cwd=short_path(self.project),
                            timeout=timeout, env=self._env(), encoding="utf8")
            output = (done.stdout or "") + (done.stderr or "")
            errors = [line for line in output.splitlines() if ": error" in line or line.startswith("error")]
            if done.returncode == 0 and not errors:
                result = (VerificationResult.PROVED, f"Certified by Lean ({self.version()}).")
                self.stats["proved"] += 1
                self._keep(path, key)
            else:
                detail = errors[0] if errors else (output.strip().splitlines() or ["no message"])[-1]
                result = (VerificationResult.UNKNOWN,
                          "Lean's arithmetic tactics (" + ", ".join(TACTICS) + ") did not close this goal: "
                          + detail.split(": error", 1)[-1].strip()[:200])
                self.stats["unknown"] += 1
        except subprocess.TimeoutExpired:
            result = (VerificationResult.UNKNOWN, f"lean exceeded {timeout:.0f}s")
            self.stats["unknown"] += 1
        finally:
            shutil.rmtree(workdir, ignore_errors=True)
        self._cache[key] = result
        return result

    def verify_many(self, obligations, timeout_ms: Optional[int] = None) -> List[Tuple[str, str]]:
        """Check several obligations in ONE Lean process.

        Almost all of the ~10 s a Lean check takes is loading Mathlib, which is paid once per
        process; a derivation's six obligations then cost about the same as one. Each obligation
        is its own theorem, so Lean's error positions say which ones failed.
        """
        results: List[Optional[Tuple[str, str]]] = [None] * len(obligations)
        todo = []                                            # (index, cache key, theorem text)
        for i, obligation in enumerate(obligations):
            try:
                single = self.source(obligation)
            except UnsupportedForBackend as e:
                results[i] = (VerificationResult.UNKNOWN, f"not translatable to Lean: {e}")
                continue
            key = hashlib.sha256(single.encode("utf8")).hexdigest()[:16]
            if key in self._cache:
                self.stats["cached"] += 1
                results[i] = self._cache[key]
            else:
                todo.append((i, key, self.theorem_text(obligation, name=f"obl_{i}")))
        if todo and not self.available:
            for i, _key, _text in todo:
                results[i] = (VerificationResult.UNKNOWN, "Lean is not installed (see FORMALLLM_LEAN_PROJECT)")
            return results                                   # type: ignore[return-value]
        if todo:
            self._run_batch(todo, results, obligations, timeout_ms)
        return results                                       # type: ignore[return-value]

    def _run_batch(self, todo, results, obligations, timeout_ms: Optional[int]) -> None:
        text = IMPORTS + "\n"
        line = text.count("\n") + 1
        spans = []                                           # (first line, last line) of each theorem
        for _i, _key, theorem in todo:
            first = line
            text += theorem + "\n"
            line += theorem.count("\n") + 1
            spans.append((first, line - 1))
        base = (timeout_ms / 1000.0) if timeout_ms and timeout_ms > 1000 else self.timeout_s
        timeout = max(base, 60.0 + 30.0 * len(todo))
        workdir = tempfile.mkdtemp(prefix="fllm_lean_")
        path = os.path.join(workdir, "batch.lean")
        with open(path, "w", encoding="utf8") as fh:
            fh.write(text)
        try:
            done = run_tree([self.lake, "env", "lean", short_path(path)], cwd=short_path(self.project),
                            timeout=timeout, env=self._env(), encoding="utf8")
            output = (done.stdout or "") + (done.stderr or "")
            first_error: Dict[int, str] = {}
            stray = None
            for message in output.splitlines():
                match = re.search(r":(\d+):\d+: error[: ](.*)", message)
                if not match:
                    continue
                at = int(match.group(1))
                owner = next((n for n, (a, b) in enumerate(spans) if a <= at <= b), None)
                if owner is None:
                    stray = stray or message
                elif owner not in first_error:
                    first_error[owner] = match.group(2).strip()
            # A non-zero exit is expected when some theorem fails. It means something global
            # (an import failed, Lean crashed) only if no error is attributed to any theorem.
            broken = bool(stray) or (done.returncode != 0 and not first_error)
            for n, (i, key, _theorem) in enumerate(todo):
                if n in first_error:
                    result = (VerificationResult.UNKNOWN,
                              "Lean's arithmetic tactics (" + ", ".join(TACTICS) + ") did not close this goal: "
                              + first_error[n][:200])
                    self.stats["unknown"] += 1
                elif broken:
                    detail = stray or (output.strip().splitlines() or ["no message"])[-1]
                    result = (VerificationResult.UNKNOWN, f"Lean failed before checking this goal: {detail[:200]}")
                    self.stats["unknown"] += 1
                else:
                    result = (VerificationResult.PROVED, f"Certified by Lean ({self.version()}).")
                    self.stats["proved"] += 1
                self._cache[key] = results[i] = result
            if self.proof_dir and not first_error and not broken and done.returncode == 0:
                os.makedirs(self.proof_dir, exist_ok=True)
                digest = hashlib.sha256(text.encode("utf8")).hexdigest()[:16]
                shutil.copy(path, os.path.join(self.proof_dir, f"batch_{digest}.lean"))
        except subprocess.TimeoutExpired:
            # One slow goal must not cost the rest: fall back to checking each on its own.
            for i, _key, _theorem in todo:
                results[i] = self.verify(obligations[i], timeout_ms)
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

    def _keep(self, path: str, key: str) -> None:
        if not self.proof_dir:
            return
        os.makedirs(self.proof_dir, exist_ok=True)
        shutil.copy(path, os.path.join(self.proof_dir, f"obl_{key}.lean"))
