"""Why a step was refused, in L_spec terms, for the model's next attempt.

Three kinds of failure, each with its own repair (and, in the selector + applier workflow, its own recipient):

* ``unreadable``: the answer is not a step (no JSON, a missing field, L_spec that does not parse or does not
  type-check). The writer fixes how it wrote the step.
* ``false``: an obligation has a counter-example. The idea is wrong: a different expression, invariant or condition.
* ``unproved``: the prover could not prove an obligation (or ran out of time); it may still be true. A simpler or
  more explicit step, or a different law.

For a loop the obligation that failed says what is wrong with the invariant, the same three ways for every loop: it
does not hold at the start, it is not kept by an iteration (a fact is missing), or it is too weak at the exit. Nothing
here depends on the task."""
from typing import Optional

from FormalLLM.dsl import steps

UNREADABLE, FALSE, UNPROVED, ACCEPTED = "unreadable", "false", "unproved", "accepted"

#: what a failed obligation means, by the engine's obligation kind (``laws.py``); ``term`` in a loop body is its own case
MEANING = {
    "init": "The invariant does not hold before the first iteration, with the initial values. Change the initial "
            "values or weaken the invariant.",
    "exit": "When the loop stops (the invariant holds and the guard is false), the goal's property does not follow for "
            "the result. The invariant must say more about what the state has computed so far (for example the "
            "property itself, stated for the part processed up to the loop variable), or the result is wrong.",
    "term_loop_body": "The next state does not keep the invariant, or the variant does not decrease. Either the update "
                      "is wrong, or the invariant is missing a fact the update relies on (add it to the invariant).",
    "term": "The value does not have the goal's property under the assumptions.",
    "wellformed": "The step does not make sense as written (a type error, or a condition that cannot be computed).",
}


def _lspec(statement: str) -> str:
    try:
        return steps.to_lspec(statement)
    except Exception:
        return statement                                   # shown as Lean rather than not at all


def kind_of(step) -> str:
    """``accepted``, ``false`` or ``unproved`` for an engine ``Step`` (``unreadable`` comes from ``StepError``)."""
    if step.ok:
        return ACCEPTED
    if step.status == "ill_formed" or any(v.status == "ILL_FORMED" for v in step.verdicts):
        return UNREADABLE
    if any(v.counterexample for v in step.verdicts if not v.proved):
        return FALSE
    return UNPROVED


def describe(step, loop_body: bool = False) -> str:
    """The refusal of an engine ``Step`` as the model reads it."""
    if step.ok:
        return "accepted"
    lines = []
    if step.status == "ill_formed" and step.message and not step.verdicts:
        return f"The step cannot be applied: {step.message}"
    for verdict in step.verdicts:
        if verdict.proved:
            continue
        kind = verdict.obligation.kind
        key = "term_loop_body" if kind == "term" and loop_body else kind
        lines.append(f"- {MEANING.get(key, verdict.obligation.description)}")
        lines.append(f"  To prove: {_lspec(closed_statement(verdict.obligation))}")
        if verdict.counterexample:
            lines.append("  It is false: " + verdict.counterexample.replace("\n", "\n  "))
        elif verdict.status == "TIMEOUT":
            lines.append("  The prover ran out of time (the statement may still be true).")
        elif verdict.status == "ILL_FORMED":
            lines.append(f"  Lean could not read it: {verdict.message[:300]}")
        else:
            lines.append("  The prover could not prove it (it may still be true; make the step simpler or more explicit).")
    return "\n".join(lines) or (step.message or step.status)


def closed_statement(obligation) -> str:
    """The obligation with its context as hypotheses: ``forall inputs, assumptions ==> statement`` (as Lean text)."""
    if obligation.body is not None:
        return obligation.statement if obligation.statement not in ("Prop", "Nat") else obligation.body
    return f"∀ {obligation.binders}, {obligation.statement}" if obligation.binders.strip() else obligation.statement


def unreadable(error: Exception) -> str:
    if isinstance(error, steps.StepError):
        return f"Your answer could not be read. In `{error.field}`: {error.message}"
    return f"Your answer could not be read: {error}"


def recipient(kind: str, attempts_on_goal: int, limit: int = 2) -> str:
    """Selector + applier workflow: who gets the failure. Writing errors and counter-examples go back to the applier;
    an unproved step, or the same goal failing ``limit`` times, goes back to the selector (the law may be wrong)."""
    if kind == UNPROVED or attempts_on_goal >= limit:
        return "selector"
    return "applier"


def lean_error(message: str, limit: int = 400) -> str:
    """Lean's error, trimmed, with the Lean names the model never wrote put back in L_spec spelling where it is
    unambiguous (``List.length`` -> ``len``, ``Nat`` -> ``nat``, ...)."""
    import re
    from FormalLLM.dsl import ops
    text = " ".join(message.split())[:limit]
    for lean, spec in list(ops.NAMES.items()) + [(f"List.{m}", f) for m, f in ops.METHOD_FUNCS.items()]:
        if lean.isidentifier() or "." in lean:
            text = re.sub(rf"(?<![\w.]){re.escape(lean)}(?![\w.])", spec, text)
    return text


def first_line(text: Optional[str]) -> str:
    return (text or "").strip().split("\n")[0][:200]
