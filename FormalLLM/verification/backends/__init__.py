"""Proof backends: Z3, Coq, Lean, and combinations.

Select with the ``FORMALLLM_BACKEND`` environment variable or pass a backend to
``RefinementEngine``:

``z3`` (default)
    Fast, finds counterexamples; no independent certificate.
``coq``
    Coq/Rocq certifies; a failure to prove is UNKNOWN (no counterexample).
``lean``
    Lean 4 + Mathlib certifies; same caveat.
``cross`` / ``cross-coq`` / ``cross-lean``
    Z3 decides and supplies counterexamples; a PROVED answer is then
    *certified* by the proof assistant, and the run records whether it was.
``z3+lean`` / ``z3+coq``
    Z3 decides; the proof assistant is asked **only when Z3 says unknown**
    (quantifiers, arrays, non-linear integers) and a proof it finds is
    accepted, kernel-checked. See ``fallback.py``.
"""

import os
from typing import Optional

from FormalLLM.verification.backends.base import ProofBackend, VerificationResult


class Z3Backend:
    name = "z3"

    def verify(self, obligation, timeout_ms: Optional[int] = None):
        from FormalLLM.verification.z3_backend import verify_obligation
        return verify_obligation(obligation, timeout_ms=timeout_ms)


def get_backend(name: Optional[str] = None) -> ProofBackend:
    """The backend called ``name`` (default: ``FORMALLLM_BACKEND`` or ``z3``)."""
    name = (name or os.environ.get("FORMALLLM_BACKEND") or "z3").lower()
    if name == "z3":
        return Z3Backend()
    if name == "coq":
        from FormalLLM.verification.backends.coq_backend import CoqBackend
        return CoqBackend()
    if name == "lean":
        from FormalLLM.verification.backends.lean_backend import LeanBackend
        return LeanBackend()
    if name in ("cross", "cross-coq", "cross-lean"):
        from FormalLLM.verification.backends.cross import CrossBackend
        return CrossBackend(certifier="lean" if name == "cross-lean" else "coq")
    if name in ("z3+lean", "z3+coq"):
        from FormalLLM.verification.backends.fallback import FallbackBackend
        return FallbackBackend(fallback=name.split("+")[1])
    raise ValueError(f"unknown backend {name!r}; choose z3, coq, lean, cross, cross-coq, cross-lean, "
                     f"z3+lean or z3+coq")
