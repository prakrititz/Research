"""Z3 first; a proof assistant only for what Z3 cannot decide.

Z3 answers almost everything in milliseconds, with a counterexample when the answer is no.
Where it gives up -- quantified statements and array reads, non-linear integers with division
-- it says "unknown", and a search that treats that as a failure can never accept a perfectly
true step. Lean's ``grind`` (or Coq's tactics) often can prove those, but slowly (about ten
seconds, almost all of it loading Mathlib), so they are asked **only when Z3 returned
unknown**, and only a *proof* is taken from them:

* Z3 says PROVED  -> accepted (as before).
* Z3 says FAILED  -> rejected with its counterexample (as before; a proof assistant adds nothing).
* Z3 says UNKNOWN -> ask the fallback. PROVED by the fallback -> accepted *and certified by its
  kernel*. Anything else -> UNKNOWN, with both reasons.

Because the fallback is only ever asked to prove, never to refute, this is strictly more capable
than Z3 alone and never accepts anything a kernel has not checked beyond what Z3 itself accepts.
"""
from typing import Optional, Tuple

from FormalLLM.verification.backends.base import VerificationResult


class FallbackBackend:
    def __init__(self, fallback: str = "lean"):
        from FormalLLM.verification.backends import Z3Backend
        self.name = f"z3+{fallback}"
        self.z3 = Z3Backend()
        if fallback == "lean":
            from FormalLLM.verification.backends.lean_backend import LeanBackend
            self.prover = LeanBackend()
        else:
            from FormalLLM.verification.backends.coq_backend import CoqBackend
            self.prover = CoqBackend()
        self.rescued = 0                      # obligations Z3 could not decide and the prover proved
        self.still_unknown = 0

    def verify(self, obligation, timeout_ms: Optional[int] = None) -> Tuple[str, str]:
        status, message = self.z3.verify(obligation, timeout_ms)
        if status != VerificationResult.UNKNOWN:
            return status, message
        proved, detail = self.prover.verify(obligation)
        if proved == VerificationResult.PROVED:
            self.rescued += 1
            return VerificationResult.PROVED, (f"Z3 could not decide this ({message.strip()[:80]}); "
                                               f"{self.prover.name} proved it. {detail}")
        self.still_unknown += 1
        return VerificationResult.UNKNOWN, f"{message} Neither could {self.prover.name} prove it: {detail[:160]}"

    @property
    def summary(self) -> str:
        return (f"{self.rescued} obligation(s) Z3 could not decide were proved by {self.prover.name}; "
                f"{self.still_unknown} stayed unknown")
