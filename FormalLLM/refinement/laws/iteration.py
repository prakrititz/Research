import copy
from typing import Dict, Any
from .base import RefinementLaw, RefinementResult
from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import Spec, Definition, BinaryOp, UnaryOp, Variable, Const, VariablePreviousState, ASTNode
from FormalLLM.lpl.ast import While, SequentialComposition
from FormalLLM.verification.proof_obligations import ProofObligation
from FormalLLM.refinement.frame import derive as _derive, rigid_context
from FormalLLM.refinement.frame import obligation_params

def to_previous_state(node: ASTNode) -> ASTNode:
    """Rewrite every variable in ``node`` to its previous-state twin (``x`` -> ``x0``).

    Note: names coming from LLM-supplied expressions are resolved to Const
    (they are not bound by any params list), so both cases must be handled or
    the variant-decrease obligation degenerates to `V < V`, i.e. false.

    Structure comes from :mod:`lspec.walk`. The previous version enumerated
    BinaryOp and UnaryOp explicitly and deep-copied anything else, so a variant
    expression containing any other compound node -- an array select, say --
    was returned with its variables *unrewritten*, again degenerating the
    obligation to `V < V`.
    """
    if isinstance(node, (Variable, Const)):
        return VariablePreviousState(node.name)
    return walk.map_children(node, to_previous_state)

def _names_in(node: ASTNode) -> set:
    """Every name ``node`` mentions, previous-state twins spelt as ``x0``."""
    names = set()
    if isinstance(node, (Variable, Const)):
        names.add(node.name)
    elif isinstance(node, VariablePreviousState):
        names.add(f"{node.name}0")
    for child in walk.children(node):
        names |= _names_in(child)
    return names


def fresh_variant_start(spec: Spec, variant_expr: ASTNode) -> Variable:
    """The paper's ``V0``: a named constant for the variant's value when the body starts.

    The body used to say ``V = V0'`` where ``V0'`` was the variant with every
    variable renamed to its previous-state twin (``N - x*x`` became
    ``N0 - x0*x0``). That is logically equivalent, but it prints as copies of
    constants that never change, and a model that read ``V0`` in the displayed
    specification and wrote it into its own formula referred to something the
    engine did not know. A real named constant is what Lemma 2.7 uses, reads
    naturally, and is the same symbol in the prompt and in the prover.

    The name is fresh: ``V0``, or ``V1`` ... if the specification already uses it
    (for example in an enclosing loop's body).
    """
    taken = (_names_in(spec.precondition.expr) | _names_in(spec.postcondition.expr)
             | _names_in(variant_expr))
    n = 0
    while f"V{n}" in taken:
        n += 1
    return Variable(f"V{n}")


def measure_bounded_while_running(spec: Spec, invariant_expr: ASTNode, guard_expr: ASTNode,
                                  variant_expr: ASTNode) -> ProofObligation:
    """``I ∧ G ⇒ 0 ≤ V``: the relaxed rule's missing half for an integer measure.

    The relaxed body postcondition only asks the measure to decrease (``V < V0``, the paper's
    Lemma 6.7 as implemented). Over the natural numbers that is enough; over the integers a measure can
    decrease for ever. Measured on the HumanEval pilot (v8, relaxed rule): ``gcd`` was derived with the
    loop ``while g is not a common divisor: g := g + 1`` and the measure ``a - g``, which decreases on every
    iteration -- and the program never stops when ``a`` does not divide ``b``. Requiring the measure to be
    non-negative *while the loop runs* closes that hole and still accepts the paper's own measure
    ``N - (x+e)²``, which only becomes negative after the last iteration (when the guard is already false).
    """
    from FormalLLM.lspec.ast import Number
    return ProofObligation(
        assumptions=[copy.deepcopy(invariant_expr), copy.deepcopy(guard_expr)],
        goal=BinaryOp(Number("0"), '<=', copy.deepcopy(variant_expr)),
        params=obligation_params(spec),
        description="termination: while the loop runs, the measure is never negative: I /\\ G => 0 <= V",
        advice=("Choose a measure that cannot become negative while the guard holds (for example the "
                "distance to the bound the loop approaches), or add to the invariant a fact that bounds it."),
    )


class IterationLaw(RefinementLaw):
    """Iteration with an LLM-supplied invariant (paper Table 5, Lemma 6.6).

        x:[P, Q]  ⊑  x:[P, I] ; while G do x:[I ∧ G, I ∧ V < V0]

    The invariant is a *parameter*, not the precondition. Previously this law
    read ``invariant = spec.precondition.expr``, which pinned I to P and left
    the initialisation branch below unreachable (``P != invariant`` could never
    be true). That restricted the law to specifications whose precondition
    already happens to be a loop invariant, and forced every other problem
    through a `sequential` step whose intermediate the model had to guess
    exactly right -- which is the one move no model in Study 3 found.

    Omitting `invariant` keeps the old behaviour (I = P), so existing scripted
    refinements and tests are unaffected.

    Obligations: P ∧ ¬G ⇒ Q.
    Sub-specs: [P ∧ G ∧ V = V0, P ∧ 0 ≤ V ∧ V < V0].
    """
    # guard and variant have no meaningful default. Defaulting the variant to
    # "0" (as this once did) yields a constant that can never decrease, so the
    # loop body becomes unprovable and the model is told its parameters were
    # wrong rather than that it forgot one.
    PARAMS = (("guard", "expr", None), ("variant", "expr", None))
    def apply(self, spec: Spec, parameters: Dict[str, Any]) -> RefinementResult:
        guard_expr = parameters.get('guard')
        variant_expr = parameters.get('variant')
        
        missing = [n for n, v in (("guard", guard_expr), ("variant", variant_expr))
                   if v is None]
        if missing:
            raise ValueError(
                f"iteration requires {' and '.join(missing)}: the guard is the "
                f"loop condition, and the variant is an expression that must "
                f"strictly decrease on every iteration so the loop terminates."
            )

        # In pure Iteration, the invariant is exactly the precondition.
        invariant_expr = spec.precondition.expr
        
        # Obligation: P ∧ ¬G ⇒ Q
        obligation = ProofObligation(
            assumptions=[copy.deepcopy(invariant_expr), UnaryOp('~', copy.deepcopy(guard_expr))],
            goal=copy.deepcopy(spec.postcondition.expr),
            params=obligation_params(spec),
            description="on exit the precondition (invariant) and the negated guard must imply the postcondition: P /\\ ~G => Q",
            advice=("Change the guard G so that the state where the loop stops (the precondition and "
                    "not G) satisfies the postcondition for these values, or use initialised_iteration "
                    "with a stronger invariant."),
        )
        
        # V0 is the variant evaluated in the pre-state of the body
        v0_expr = fresh_variant_start(spec, variant_expr)
        
        # Sub-spec precondition: I ∧ G ∧ (V = V0)
        pre_expr = BinaryOp(copy.deepcopy(invariant_expr), '/\\', copy.deepcopy(guard_expr))
        # Capture the variant's pre-state value. Without the V = V0 conjunct, V0 is an
        # unconstrained logical constant and no loop body can ever be verified.
        pre_expr = BinaryOp(pre_expr, '/\\',
                            BinaryOp(copy.deepcopy(variant_expr), '=', copy.deepcopy(v0_expr)))

        # Sub-spec postcondition: P ∧ (0 ≤ V) ∧ (V < V0) if strict, else P ∧ (V < V0)
        from FormalLLM.lspec.ast import Number
        import os
        strict = os.environ.get("FORMALLLM_STRICT_VARIANT", "1") == "1"
        v_decreases = BinaryOp(copy.deepcopy(variant_expr), '<', v0_expr)
        
        obligations = [obligation]
        if strict:
            zero = Number("0")
            v_lower_bound = BinaryOp(zero, '<=', copy.deepcopy(variant_expr))
            variant_cond = BinaryOp(v_lower_bound, '/\\', v_decreases)
        else:
            variant_cond = v_decreases
            obligations.append(measure_bounded_while_running(spec, invariant_expr, guard_expr, variant_expr))

        post_expr = BinaryOp(copy.deepcopy(invariant_expr), '/\\', variant_cond)

        body_spec = _derive(spec,
            precondition=Definition(None, copy.deepcopy(spec.precondition.params), pre_expr),
            postcondition=Definition(None, copy.deepcopy(spec.postcondition.params), post_expr)
        )

        return RefinementResult(
            sub_specs=[body_spec],
            obligations=obligations,
            roles=["body"],
        )

    @classmethod
    def build_program(cls, parameters, children):
        return While(parameters["guard"], children["body"])
