import os
import z3
from typing import List, Optional, Tuple
from .proof_obligations import ProofObligation
from FormalLLM.lspec.z3_translator import Z3Translator
from FormalLLM.lspec.ast import Variable


class VerificationResult:
    PROVED = "PROVED"
    FAILED = "FAILED"
    UNKNOWN = "UNKNOWN"


#: Wall-clock budget for one obligation. Without a limit, a nonlinear or
#: quantified obligation can run unboundedly and stall an entire refinement run;
#: with one, Z3 answers `unknown` and the refiner records the attempt as
#: INCONCLUSIVE and moves on. Override with FORMALLLM_Z3_TIMEOUT_MS.
DEFAULT_TIMEOUT_MS = 10_000

#: How long Z3 takes on a hard obligation is wildly uneven. The very same obligation is proved in a few
#: milliseconds on one run and runs into the 10 s limit on the next, because the search depends on the
#: numbering of the terms and on the random seed (measured on the loop body of a primality check: the
#: same derivation was proved in 1 s or rejected after 10 s; 7 of 12 seeds proved the obligation in under
#: 10 ms, the others timed out). So an obligation is first tried in a few short runs, each built from
#: scratch with its own random seed, and only then in one patient run with the whole budget. Every
#: attempt can only turn "unknown" into a proof or a counterexample; a proof is a proof whatever the
#: seed. Only calls that use the default budget do this (a model's proposal, not the assist's many cheap
#: guesses). FORMALLLM_Z3_RETRIES=0 turns it off (one run with the whole budget).
DEFAULT_RETRIES = 4
RETRY_MIN_MS = 300
RETRY_STATS = {"rescued": 0, "gave_up": 0}


def _retries() -> int:
    raw = os.environ.get("FORMALLLM_Z3_RETRIES")
    try:
        return max(0, int(raw)) if raw else DEFAULT_RETRIES
    except ValueError:
        return DEFAULT_RETRIES


def _timeout_ms() -> int:
    raw = os.environ.get("FORMALLLM_Z3_TIMEOUT_MS")
    try:
        return int(raw) if raw else DEFAULT_TIMEOUT_MS
    except ValueError:
        return DEFAULT_TIMEOUT_MS


def _array_text(value):
    """An array value as a reader can take it: ``[0] = 2438, every other element 2437``.

    Z3 prints array values in its own notation (``Store(K(Int, 2437), 0, 2438)``). Measured on the HumanEval
    pilot (v8): array counterexamples were shown to the model exactly like that, next to otherwise readable
    values. ``None`` when ``value`` is not a constant array with stores on top.
    """
    stores = []
    while z3.is_store(value):
        stores.append((value.arg(1), value.arg(2)))
        value = value.arg(0)
    if not z3.is_K(value):
        return None
    default = _value_text(value.arg(0))
    seen, parts = set(), []
    for index, element in stores:                       # the outermost store wins for a repeated index
        key = _value_text(index)
        if key in seen:
            continue
        seen.add(key)
        parts.append(f"[{key}] = {_value_text(element)}")
    parts.sort()
    every = f"every element {default}" if not parts else f"every other element {default}"
    return ", ".join(parts + [every])


def _value_text(value) -> str:
    """A model value as short text (rationals as n/d, irrationals approximately, arrays element by element)."""
    try:
        if z3.is_array(value):
            text = _array_text(value)
            if text is not None:
                return text
        if z3.is_rational_value(value):
            num, den = value.numerator_as_long(), value.denominator_as_long()
            return str(num) if den == 1 else f"{num}/{den}"
        if z3.is_int_value(value):
            return str(value.as_long())
        if z3.is_algebraic_value(value):
            approx = value.approx(10)
            return f"about {approx.numerator_as_long() / approx.denominator_as_long():.6g}"
    except Exception:
        pass
    return str(value)


class FailureExplanation:
    """What a rejected obligation looks like to a reader.

    ``assumptions`` and ``goal`` are bullet lists in the readable syntax;
    ``values`` is the counterexample restricted to names the reader can see;
    ``violated`` lists the conjuncts of the goal that are false for it.
    """

    def __init__(self, assumptions: str, goal: str, values: str, violated: List[str]):
        self.assumptions = assumptions
        self.goal = goal
        self.values = values
        self.violated = violated


def explain_counterexample(obligation: ProofObligation, model,
                           translator: Optional[Z3Translator] = None) -> FailureExplanation:
    """Render a rejected obligation and its counterexample for a reader.

    The raw model lists every solver variable, including the previous-state
    copies (``N0``, ``x0``, ``e0``) the loop laws introduce for the variant's
    starting value -- values nobody can act on. Here those are folded into
    ``V0``, only names that appear in the displayed formulas are listed, and
    each conjunct of the goal is evaluated under the model so the reader is told
    *which* requirement the counterexample breaks.
    """
    from FormalLLM.llm import spec_render as sr

    if translator is None:
        translator = Z3Translator()
        translator.declare_params(getattr(obligation, "params", []))

    exprs = list(obligation.assumptions) + [obligation.goal]
    shown, abbreviations = sr.abbreviate_variant_starts(exprs)
    shown_assumptions, shown_goal = shown[:-1], shown[-1]

    def evaluate(expr):
        return model.eval(translator.translate(expr), model_completion=True)

    mentioned = set()
    for expr in shown:
        mentioned |= sr.mentioned_names(expr)
    # V0, V1 ... are display names for expressions, not solver variables; their
    # values are computed from the expressions below.
    mentioned -= set(abbreviations)

    parts = []
    for name in sorted(mentioned):
        try:
            parts.append(f"{name} = {_value_text(evaluate(Variable(name)))}")
        except Exception:
            continue
    for name, (_variant, start) in abbreviations.items():
        try:
            parts.append(f"{name} = {_value_text(evaluate(start))}")
        except Exception:
            continue

    violated = []
    for conjunct in sr.conjuncts(obligation.goal):
        try:
            if z3.is_false(evaluate(conjunct)):
                violated.append(sr.render_expr(sr.apply_abbreviations(conjunct, abbreviations)))
        except Exception:
            continue

    assumptions = "\n".join(sr.bullets(a, indent="    ") for a in shown_assumptions)
    return FailureExplanation(assumptions, sr.bullets(shown_goal, indent="    "),
                              ", ".join(parts), violated)


def describe_failure(obligation: ProofObligation, model,
                     translator: Optional[Z3Translator] = None) -> str:
    """Explain a rejected obligation in terms the model can act on.

    A bare list of variable assignments says nothing about which choice was
    wrong. Measured on the paper's square-root example: the loop body was
    rejected with `x = -2`, which is precisely the evidence that the proposed
    invariant failed to exclude negative x -- but nothing in the message said
    so, and the model responded by abandoning the (correct) law rather than
    strengthening its invariant.
    """
    explanation = explain_counterexample(obligation, model, translator)

    lines = []
    if obligation.description:
        lines.append(f"The obligation that failed: {obligation.description}")
    if explanation.assumptions:
        lines.append("  assuming:")
        lines.append(explanation.assumptions)
    lines.append("  must show:")
    lines.append(explanation.goal)
    if explanation.values:
        lines.append("Counterexample (these values satisfy the assumptions but falsify the goal): "
                     + explanation.values)
        if explanation.violated:
            lines.append("For these values the following part of the goal is false:")
            lines.extend(f"    - {text}" for text in explanation.violated)
        lines.append(getattr(obligation, "advice", None)
                     or "Change the parameters of this step so that this case cannot arise.")
    return "\n".join(lines)


def _attempt(obligation: ProofObligation, timeout_ms: int, seed: Optional[int] = None):
    """One Z3 run on ``obligation``, from a fresh solver (with random seed ``seed`` if given)."""
    translator = Z3Translator()
    translator.declare_params(getattr(obligation, "params", []))
    solver = z3.Solver()
    solver.set("timeout", timeout_ms)
    if seed is not None:
        solver.set("random_seed", seed)
        solver.set("smt.random_seed", seed)

    for assumption in obligation.assumptions:
        solver.add(translator.translate(assumption))
    solver.add(z3.Not(translator.translate(obligation.goal)))
    return solver, translator, solver.check()


def _ran_out_of_time(solver) -> bool:
    reason = (solver.reason_unknown() or "").lower()
    return "timeout" in reason or "canceled" in reason or "resource" in reason


def _plan(budget_ms: int, retries: int):
    """The runs to make, as (time limit, seed): ``retries`` short ones, then one with the whole budget."""
    if retries <= 0:
        return [(budget_ms, None)]
    short = max(RETRY_MIN_MS, budget_ms // 10)
    return [(short, None)] + [(short, seed) for seed in range(1, retries)] + [(budget_ms, retries)]


def _solve(obligation: ProofObligation, timeout_ms: Optional[int], retries: int = 0):
    budget = timeout_ms if timeout_ms is not None else _timeout_ms()
    plan = _plan(budget, retries)
    for index, (limit, seed) in enumerate(plan):
        try:
            solver, translator, result = _attempt(obligation, limit, seed)
        except z3.Z3Exception:
            if seed is None:
                raise
            solver, translator, result = _attempt(obligation, limit)     # a Z3 build without the seed parameters
        timed_out = result == z3.unknown and _ran_out_of_time(solver)
        if not timed_out or index == len(plan) - 1:
            if index > 0 and result != z3.unknown:
                RETRY_STATS["rescued"] += 1
            if retries and timed_out:
                RETRY_STATS["gave_up"] += 1
            return solver, translator, result
        # Let Z3 free this run's terms before the next one: a run built from scratch gets new term
        # numbers, which changes the search as much as the seed does.
        del solver, translator, result


def verify_obligation(obligation: ProofObligation, timeout_ms: Optional[int] = None) -> Tuple[str, str]:
    """
    Verifies a proof obligation using Z3.
    Returns (status, message_or_counterexample)
    """
    try:
        solver, translator, result = _solve(obligation, timeout_ms, _retries() if timeout_ms is None else 0)
        if result == z3.unsat:
            return VerificationResult.PROVED, "Obligation is logically valid."
        elif result == z3.sat:
            return VerificationResult.FAILED, describe_failure(obligation, solver.model(), translator)
        else:
            return VerificationResult.UNKNOWN, f"Solver returned unknown: {solver.reason_unknown()}"

    except Exception as e:
        return VerificationResult.UNKNOWN, f"Translation or solver error: {str(e)}"


def check_implication(obligation: ProofObligation, timeout_ms: int = 3000) -> Tuple[str, str]:
    """Decide ``assumptions => goal`` and, if it fails, return the counterexample values.

    Used to tell a prompt reader facts the prover can settle (for example "skip
    is not valid, because these values satisfy P but not Q") without making
    them parse a failure message.
    """
    try:
        solver, translator, result = _solve(obligation, timeout_ms)
        if result == z3.unsat:
            return VerificationResult.PROVED, ""
        if result == z3.sat:
            return (VerificationResult.FAILED,
                    explain_counterexample(obligation, solver.model(), translator).values)
        return VerificationResult.UNKNOWN, ""
    except Exception:
        return VerificationResult.UNKNOWN, ""
