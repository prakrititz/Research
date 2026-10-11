import os
from typing import Dict, Any, Optional, Type
from FormalLLM.lspec.ast import Spec
from .laws.base import RefinementLaw, RefinementResult
from .laws.registry import LAWS
from FormalLLM.verification.z3_backend import verify_obligation, VerificationResult
from FormalLLM.verification.backends import get_backend
from .feasibility import feasibility_obligations
from .relevance import pointless_test_message, pointless_test_variables, unexecutable_guard_message
from .value_kinds import assignment_type_error

#: A quick necessary-condition check must never stall a search.
ADVISORY_TIMEOUT_MS = 3000


class VerificationError(Exception):
    pass

class VerificationUnknown(VerificationError):
    """The solver could neither prove nor refute the obligation (timeout,
    nonlinear arithmetic, quantifiers, translation failure). Distinct from a
    refutation: the parameters may be fine, so callers must not treat it as a
    counterexample. A subclass so existing `except VerificationError` still works."""

class RefinementEngine:
    def __init__(self, backend=None, check_feasibility: Optional[bool] = None):
        # A per-engine copy of the registry, so a caller may restrict the law
        # set (the benchmark harness does, to make the law set the only
        # variable between arms) without mutating the global registry.
        self.laws: Dict[str, Type[RefinementLaw]] = dict(LAWS)
        # Who proves the obligations: Z3 (default), Coq, Lean, or Z3 with a proof
        # assistant certifying -- see verification/backends. FORMALLLM_BACKEND picks.
        self.backend = backend if backend is not None else get_backend()
        # Every sub-specification a step creates must be feasible (see feasibility.py).
        # On by default; FORMALLLM_FEASIBILITY=0 switches it off, for ablation.
        if check_feasibility is None:
            check_feasibility = os.environ.get("FORMALLLM_FEASIBILITY", "1") != "0"
        self.check_feasibility = check_feasibility

    def register_law(self, name: str, law_cls: Type[RefinementLaw]):
        self.laws[name] = law_cls

    def apply(self, spec: Spec, law_name: str, parameters: Dict[str, Any],
              timeout_ms: Optional[int] = None) -> RefinementResult:
        if law_name not in self.laws:
            raise ValueError(f"Unknown refinement law: {law_name}")
            
        law = self.laws[law_name]()
        result = law.apply(spec, parameters)

        # A split on a test about a variable whose starting value is arbitrary cannot help.
        if law_name == "alternation":
            pointless = pointless_test_variables(spec, parameters.get("guard"))
            if pointless:
                raise VerificationError("Refinement invalid. " + pointless_test_message(spec, pointless))
        
        # A guard is a test the finished program must be able to run.
        if "guard" in parameters:
            unexecutable = unexecutable_guard_message(parameters.get("guard"))
            if unexecutable:
                raise VerificationError("Refinement invalid. " + unexecutable)

        # The value assigned must be of the variable's type (Z3 would read 0 as false).
        if law_name == "assignment" and parameters.get("variable") and parameters.get("expr") is not None:
            ill_typed = assignment_type_error(spec, parameters["variable"], parameters["expr"])
            if ill_typed:
                raise VerificationError("Refinement invalid. " + ill_typed)

        # Verify obligations
        for obligation in result.obligations:
            status, msg = self.backend.verify(obligation, timeout_ms)
            if status == VerificationResult.FAILED:
                raise VerificationError(f"Refinement invalid. {msg}")
            elif status == VerificationResult.UNKNOWN:
                raise VerificationUnknown(f"Refinement verification unknown. {msg}")
                
        # Necessary conditions for the sub-specifications to be refinable at all: each one
        # must be feasible (pre => exists frame. post). Only a genuine counterexample rejects
        # the step; "unknown" is never held against it. Z3 answers these whatever backend
        # certifies the obligations above: a proof assistant says nothing useful about a failure.
        advisory = list(getattr(result, "advisory", []))
        if self.check_feasibility:
            advisory += feasibility_obligations(law_name, result)
        result.advisory = advisory
        for obligation in advisory:
            limit = getattr(obligation, "budget_ms", None) or ADVISORY_TIMEOUT_MS
            status, msg = verify_obligation(obligation, min(timeout_ms or limit, limit))
            if status == VerificationResult.FAILED:
                raise VerificationError(f"Refinement invalid. {msg}")

        return result
