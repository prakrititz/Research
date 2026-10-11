"""Feasibility: is any program a candidate for this sub-specification?

Morgan calls a specification ``x : [pre, post]`` *feasible* when every state that
satisfies ``pre`` can be followed by a state that satisfies ``post``:

    pre  =>  exists x'. post

An infeasible specification cannot be refined to any program (only to the
"miracle" ``magic``, which this calculus does not have). So when a step produces
one, the step is doomed whatever else the derivation does below it, and the
quickest honest answer is a counterexample: *these* values, and no way forward.

Measured on the paper's square-root example: a loop whose invariant contained the
guard's own condition (``N >= (x+e)^2``) has a body that is infeasible whenever
``N = (x+e)^2`` -- no next state both keeps the invariant and makes progress. The
search spent all 30 of its LLM calls below that loop body. The set-up step
``[P, I]`` is the special case of this check that was already in place.

This is a *necessary* condition, not part of any law's soundness, so it is never
certified: a refutation rejects the step; "proved", "unknown" and "timed out" are
all ignored. A specification that mentions previous-state variables is skipped,
because the existential would then have to be tied to the value before the step.
"""

import copy
from typing import List, Optional, Tuple

from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import FloatType, Param, QuantifiedExpr, VariablePreviousState

#: Allowance for a feasibility check over a specification that quantifies (arrays, `forall`).
QUANTIFIED_BUDGET_MS = 300
from FormalLLM.refinement.frame import obligation_params
from FormalLLM.verification.proof_obligations import ProofObligation

_BODY = (
    "the loop body must be possible: from every state where the invariant and the guard hold there "
    "must be a next state that satisfies the invariant and has a smaller variant",
    "From these values no next state keeps the invariant and lowers the variant, so no loop body can "
    "exist. Compare the values with your invariant, guard and variant. (a) If they are states the loop "
    "can never reach, add a fact to the invariant that excludes them. (b) If the invariant restates the "
    "guard or pins a variable, it forbids progress: weaken it. (c) If the variant cannot decrease from "
    "here (it is already at its smallest), choose a different variant or guard.",
)

#: ``(law, role) -> (what is checked, what to change)``.
_NOTES = {
    ("initialised_iteration", "init"): (
        "the set-up step must be possible: for every input satisfying the precondition there must be "
        "values of the frame variables that satisfy the invariant",
        "The invariant is too strong: for these inputs no values of the frame variables satisfy it, so "
        "no set-up step can establish it. Weaken I (drop or relax a conjunct)."),
    ("initialised_iteration", "body"): _BODY,
    ("iteration", "body"): (
        _BODY[0],
        "From these values no next state keeps the precondition (the invariant) and lowers the "
        "variant. Change the guard G or the variant V, or use initialised_iteration with an invariant "
        "that excludes these values."),
    ("sequential", "part1"): (
        "the first stage must be possible: from every state satisfying the precondition there must be a "
        "state satisfying R",
        "R cannot be reached from these values. Weaken R: it must hold in some state reachable from every input."),
    ("sequential", "part2"): (
        "the second stage must be possible: from every state satisfying R there must be a state "
        "satisfying the postcondition",
        "R allows these values, from which the postcondition cannot be reached. Strengthen R to exclude "
        "them, or choose a different R."),
    ("flexible_sequential", "part1"): (
        "the first stage must be possible: from every state satisfying A there must be a state satisfying B",
        "B cannot be reached from these values. Weaken B, or strengthen A to exclude them."),
    ("flexible_sequential", "part2"): (
        "the second stage must be possible: from every state satisfying C there must be a state satisfying D",
        "From these values D cannot be reached. Strengthen C to exclude them, or weaken D."),
    ("strengthen_post", "sub"): (
        "the strengthened specification must be possible: from every state satisfying P there must be a "
        "state satisfying R",
        "R is too strong: for these values no state satisfies it. Choose a weaker R that still implies Q."),
    ("weaken_pre", "sub"): (
        "the weakened specification must be possible: from every state satisfying R there must be a state "
        "satisfying Q",
        "R allows these values, from which Q cannot be reached. Choose a stronger R that P still implies."),
    ("alternation", "then"): (
        "the first case must be possible: from every state satisfying P and the test G there must be a "
        "state satisfying Q",
        "In this case Q cannot be reached. Choose a different test G."),
    ("alternation", "else"): (
        "the second case must be possible: from every state satisfying P and not G there must be a state "
        "satisfying Q",
        "In this case Q cannot be reached. Choose a different test G."),
}

_DEFAULT = (
    "the sub-specification '{role}' must be possible: from every state satisfying its precondition some "
    "state must satisfy its postcondition",
    "No program can satisfy that sub-specification for these values. Change the parameters that define it.",
)


def notes_for(law_name: str, role: str) -> Tuple[str, str]:
    description, advice = _NOTES.get((law_name, role), _DEFAULT)
    return description.format(role=role), advice


def _mentions_previous_state(spec) -> bool:
    def visit(node) -> bool:
        if isinstance(node, VariablePreviousState):
            return True
        return any(visit(child) for child in walk.children(node))
    return visit(spec.precondition.expr) or visit(spec.postcondition.expr)


def _quantifies(spec) -> bool:
    def visit(node) -> bool:
        if isinstance(node, QuantifiedExpr):
            return True
        return any(visit(child) for child in walk.children(node))
    return visit(spec.precondition.expr) or visit(spec.postcondition.expr)


def _binders(spec) -> List[Param]:
    """The frame variables as quantifier binders, each with the type the specification gives it."""
    declared = {p.name: p.type_ for p in list(spec.precondition.params) + list(spec.postcondition.params)}
    out = []
    for entry in spec.frame:
        name = getattr(entry, "name", entry)
        type_ = declared.get(name) or getattr(entry, "type_", None) or FloatType()
        out.append(Param(name, type_))
    return out


def feasibility_obligation(law_name: str, role: str, spec) -> Optional[ProofObligation]:
    """``pre => exists frame. post`` for ``spec``, or ``None`` if it cannot be stated."""
    if not spec.frame or _mentions_previous_state(spec):
        return None
    description, advice = notes_for(law_name, role)
    return ProofObligation(
        assumptions=[copy.deepcopy(spec.precondition.expr)],
        goal=QuantifiedExpr("exists", _binders(spec), copy.deepcopy(spec.postcondition.expr)),
        params=obligation_params(spec),
        description=description,
        advice=advice,
        budget_ms=QUANTIFIED_BUDGET_MS if _quantifies(spec) else None,
    )


def feasibility_obligations(law_name: str, result) -> List[ProofObligation]:
    """One feasibility obligation per sub-specification of a law application."""
    out = []
    for role, sub in result.by_role().items():
        obligation = feasibility_obligation(law_name, role, sub)
        if obligation is not None:
            out.append(obligation)
    return out
