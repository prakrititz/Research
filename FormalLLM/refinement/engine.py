import os
from typing import Dict, Any, Optional, Type
from FormalLLM.lspec.ast import Spec
from .laws.base import RefinementLaw, RefinementResult
from .laws.registry import LAWS
from FormalLLM.verification.z3_backend import verify_obligation, VerificationResult
from FormalLLM.verification.backends import get_backend
from .feasibility import feasibility_obligations
from .relevance import (has_quantifier, pointless_test_message, pointless_test_variables, proof_only_message,
                        proof_only_names, unexecutable_guard_message)
from .value_kinds import assignment_type_error

#: The quick "is this test already decided?" check: a short limit, and "unknown" never refuses a step.
DECIDED_TIMEOUT_MS = 1500


def decided_guard_message(spec, guard) -> str:
    """Why an ``if`` on ``guard`` cannot help here, or ``""``.

    If the precondition already implies the test (or its negation), one branch can never run and the other is
    the original problem again. Measured on the HumanEval pilot (v8): the model split an ``else`` branch on the
    same test as its parent, again and again; every new ``then`` branch had a contradictory precondition, was
    closed by ``skip``, and the 30 calls ran out without progress (the progress check only caught textually
    identical sub-problems). Only a proof refuses; an undecided check lets the step through.
    """
    import copy
    from FormalLLM.lspec.ast import UnaryOp
    from FormalLLM.refinement.frame import obligation_params
    from FormalLLM.verification.proof_obligations import ProofObligation
    from FormalLLM.verification.z3_backend import check_implication
    for goal, side in ((guard, "else"), (UnaryOp("~", copy.deepcopy(guard)), "then")):
        obligation = ProofObligation(assumptions=[copy.deepcopy(spec.precondition.expr)], goal=copy.deepcopy(goal),
                                     params=obligation_params(spec))
        status, _ = check_implication(obligation, timeout_ms=DECIDED_TIMEOUT_MS)
        if status == VerificationResult.PROVED:
            truth = "true" if side == "else" else "false"
            return (f"The test is already decided here: the precondition makes it always {truth}, so the {side} "
                    f"branch could never run and the other branch is the same problem as before. Test something "
                    f"the precondition leaves open, or choose another law.")
    return ""

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
            ghosts = proof_only_names(parameters.get("guard"))
            if ghosts:
                raise VerificationError("Refinement invalid. " + proof_only_message(ghosts, "test"))

        # A split whose test the precondition already decides has a branch that can never run.
        if law_name == "alternation" and parameters.get("guard") is not None:
            decided = decided_guard_message(spec, parameters["guard"])
            if decided:
                raise VerificationError("Refinement invalid. " + decided)

        # The value assigned must be of the variable's type (Z3 would read 0 as false), and computable.
        if law_name == "assignment" and parameters.get("variable") and parameters.get("expr") is not None:
            ill_typed = assignment_type_error(spec, parameters["variable"], parameters["expr"])
            if ill_typed:
                raise VerificationError("Refinement invalid. " + ill_typed)
            # v8 pilot, iscube: t := (exists k. k*k*k = a) was proved (trivially) and could not be run.
            if has_quantifier(parameters["expr"]):
                raise VerificationError(
                    "Refinement invalid. The value uses a quantifier (exists/forall). A program cannot evaluate a "
                    "quantifier over all integers; compute the answer with a loop that searches the range, and keep "
                    "the quantifier in the loop's invariant.")
            ghosts = proof_only_names(parameters["expr"])
            if ghosts:
                raise VerificationError("Refinement invalid. " + proof_only_message(ghosts, "value"))

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
