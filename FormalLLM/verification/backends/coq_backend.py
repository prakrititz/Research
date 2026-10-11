"""Certify proof obligations with Coq / Rocq.

Each obligation is printed as a Coq goal (see :mod:`lspec.coq_translator`),
closed by a cascade of arithmetic tactics, and checked by ``coqc``. A successful
run means Coq's kernel accepted a proof, which is what the paper's Coq-based
pipeline provides and Z3 alone does not.

``coqc`` failing to prove a goal is **not** a refutation -- the tactics may
simply be too weak -- so that case is reported as UNKNOWN, never FAILED.

Installation: on this machine Rocq Platform 2026.07.0 (Rocq 9.1) lives in
``~/.formalllm/rocq``; ``FORMALLLM_COQC`` or ``coqc`` on PATH override it.
"""

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from typing import Dict, Optional, Tuple

from FormalLLM.lspec.coq_translator import UnsupportedForBackend, obligation_to_coq
from FormalLLM.verification.backends.base import VerificationResult
from FormalLLM.verification.backends.process import run_tree

#: Tactics tried, in order, on every conjunct of the goal. ``lia``/``nia`` are
#: for integers, ``lra``/``nra`` for reals (Fourier-Motzkin plus products of
#: hypotheses); ``tauto`` closes purely propositional leftovers. ``subst`` first
#: replaces a variable that an equation pins (``x = 0``), which the arithmetic
#: tactics cannot do across an integer-to-real cast.
TACTICS = ("lia", "lra", "nia", "nra", "tauto", "(subst; lra)", "(subst; nra)")


def find_coqc() -> Optional[str]:
    explicit = os.environ.get("FORMALLLM_COQC")
    if explicit and os.path.exists(explicit):
        return explicit
    home = os.path.join(os.path.expanduser("~"), ".formalllm", "rocq", "bin", "coqc.exe")
    if os.path.exists(home):
        return home
    return shutil.which("coqc")


class CoqBackend:
    name = "coq"

    def __init__(self, coqc: Optional[str] = None, timeout_s: float = 60.0,
                 proof_dir: Optional[str] = None):
        self.coqc = coqc or find_coqc()
        self.timeout_s = timeout_s
        self.proof_dir = proof_dir or os.environ.get("FORMALLLM_PROOF_DIR")
        self._cache: Dict[str, Tuple[str, str]] = {}
        self._version: Optional[str] = None
        self.stats = {"proved": 0, "unknown": 0, "cached": 0}

    # --- environment --------------------------------------------------------

    @property
    def available(self) -> bool:
        return bool(self.coqc) and os.path.exists(self.coqc)

    def version(self) -> str:
        if self._version is None:
            out = subprocess.run([self.coqc, "--version"], capture_output=True, text=True, timeout=30)
            self._version = (out.stdout or out.stderr).strip().splitlines()[0]
        return self._version

    def _library_prefix(self) -> str:
        """Rocq 9 renamed the standard library from ``Coq`` to ``Stdlib``."""
        match = re.search(r"version (\d+)", self.version())
        return "Stdlib" if match and int(match.group(1)) >= 9 else "Coq"

    # --- source -------------------------------------------------------------

    def source(self, obligation) -> str:
        statement, _sorts = obligation_to_coq(obligation)
        tactics = " | ".join(TACTICS)
        description = (getattr(obligation, "description", None) or "proof obligation").replace("\n", " ")
        return (
            f"(* {description} *)\n"
            f"From {self._library_prefix()} Require Import Reals Lra Psatz ZArith Lia.\n\n"
            f"Goal {statement}.\n"
            f"Proof.\n"
            f"  intros.\n"
            f"  repeat split.\n"
            f"  all: first [ {tactics} ].\n"
            f"Qed.\n"
        )

    # --- verification -------------------------------------------------------

    def verify(self, obligation, timeout_ms: Optional[int] = None) -> Tuple[str, str]:
        if not self.available:
            return VerificationResult.UNKNOWN, "coqc is not installed (set FORMALLLM_COQC)"
        try:
            text = self.source(obligation)
        except UnsupportedForBackend as e:
            return VerificationResult.UNKNOWN, f"not translatable to Coq: {e}"

        key = hashlib.sha256(text.encode("utf8")).hexdigest()[:16]
        if key in self._cache:
            self.stats["cached"] += 1
            return self._cache[key]

        timeout = (timeout_ms / 1000.0) if timeout_ms else self.timeout_s
        workdir = tempfile.mkdtemp(prefix="fllm_coq_")
        path = os.path.join(workdir, f"obl_{key}.v")
        with open(path, "w", encoding="utf8") as fh:
            fh.write(text)
        try:
            done = run_tree([self.coqc, "-q", os.path.basename(path)], cwd=workdir, timeout=timeout)
            if done.returncode == 0:
                result = (VerificationResult.PROVED, f"Certified by {self.version()}.")
                self.stats["proved"] += 1
                self._keep(path, key)
            else:
                detail = (done.stdout + done.stderr).strip().splitlines()
                result = (VerificationResult.UNKNOWN,
                          "Coq's arithmetic tactics (" + ", ".join(TACTICS) + ") did not close this goal: "
                          + (detail[-1] if detail else "no message"))
                self.stats["unknown"] += 1
        except subprocess.TimeoutExpired:
            result = (VerificationResult.UNKNOWN, f"coqc exceeded {timeout:.0f}s")
            self.stats["unknown"] += 1
        finally:
            shutil.rmtree(workdir, ignore_errors=True)
        self._cache[key] = result
        return result

    def _keep(self, path: str, key: str) -> None:
        """Leave the proof script behind so a certified run can be audited."""
        if not self.proof_dir:
            return
        os.makedirs(self.proof_dir, exist_ok=True)
        shutil.copy(path, os.path.join(self.proof_dir, f"obl_{key}.v"))
