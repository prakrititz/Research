"""The interface every proof backend implements.

``verify`` answers the question the engine asks of an obligation: is
``assumptions => goal`` valid? The three answers mean different things for
different tools, and the difference matters:

``PROVED``
    The tool established validity. For Coq and Lean this is a *certificate*: a
    small trusted kernel checked a proof script, which is auditable.
``FAILED``
    The tool found a counterexample. Only a solver that builds models (Z3) can
    say this; a proof assistant failing to prove something refutes nothing.
``UNKNOWN``
    No answer: a timeout, an unsupported construct, or "my tactics did not
    find a proof". For a proof assistant this is its normal way of saying no.
"""

from typing import Optional, Protocol, Tuple

from FormalLLM.verification.proof_obligations import ProofObligation


class VerificationResult:
    PROVED = "PROVED"
    FAILED = "FAILED"
    UNKNOWN = "UNKNOWN"


class ProofBackend(Protocol):
    name: str

    def verify(self, obligation: ProofObligation,
               timeout_ms: Optional[int] = None) -> Tuple[str, str]:
        """Return ``(status, message)``; ``message`` explains a FAILED or UNKNOWN."""
        ...
