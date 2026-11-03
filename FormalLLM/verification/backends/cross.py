"""Z3 decides; a proof assistant certifies.

The two tools are good at different things. Z3 refutes: when an obligation is
false it returns concrete values, which are what a model needs to repair its
parameters. Coq and Lean certify: when an obligation is true they can leave a
proof that a small kernel has checked, which Z3's "unsat" does not give.

``CrossBackend`` therefore asks Z3 first. A counterexample goes straight back.
If Z3 proves the obligation, the proof assistant is asked to certify it, and the
backend remembers whether it could -- by default a certification failure does
**not** reject the step (the tactics may just be weaker than Z3), but it is
counted and listed, so a run can state "N of M obligations were machine-checked".
Set ``require_certificate=True`` to reject uncertified obligations instead.
"""

from typing import List, Optional, Tuple

from FormalLLM.verification.backends.base import VerificationResult


class CrossBackend:
    def __init__(self, certifier: str = "coq", require_certificate: bool = False):
        from FormalLLM.verification.backends import Z3Backend
        self.name = f"cross-{certifier}"
        self.z3 = Z3Backend()
        if certifier == "lean":
            from FormalLLM.verification.backends.lean_backend import LeanBackend
            self.certifier = LeanBackend()
        else:
            from FormalLLM.verification.backends.coq_backend import CoqBackend
            self.certifier = CoqBackend()
        self.require_certificate = require_certificate
        self.certified = 0
        self.uncertified: List[str] = []

    def verify(self, obligation, timeout_ms: Optional[int] = None) -> Tuple[str, str]:
        status, message = self.z3.verify(obligation, timeout_ms)
        if status != VerificationResult.PROVED:
            return status, message
        cert_status, cert_message = self.certifier.verify(obligation, timeout_ms)
        if cert_status == VerificationResult.PROVED:
            self.certified += 1
            return VerificationResult.PROVED, f"Obligation is logically valid. {cert_message}"
        description = getattr(obligation, "description", None) or "obligation"
        self.uncertified.append(f"{description}: {cert_message}")
        if self.require_certificate:
            return VerificationResult.UNKNOWN, f"Z3 proved it but {self.certifier.name} could not certify it. {cert_message}"
        return VerificationResult.PROVED, f"Obligation is logically valid (not certified by {self.certifier.name}: {cert_message})"

    @property
    def summary(self) -> str:
        total = self.certified + len(self.uncertified)
        return f"{self.certified} of {total} proved obligations were certified by {self.certifier.name}"
