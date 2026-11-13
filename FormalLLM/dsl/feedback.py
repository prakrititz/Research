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


def _lspec(statement: str, scope=()) -> str:
    try:
        return steps.to_lspec(statement, "statement", scope)
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


def describe(step, loop_body: bool = False, scope=()) -> str:
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
        lines.append(f"  To prove: {_lspec(closed_statement(verdict.obligation), scope)}")
        if verdict.counterexample:
            lines.append("  It is false: " + _counterexample(verdict.counterexample, scope).replace("\n", "\n  "))
        elif verdict.status == "TIMEOUT":
            lines.append("  The prover ran out of time (the statement may still be true).")
        elif verdict.status == "ILL_FORMED":
            lines.append(f"  Lean could not read it: {verdict.message[:300]}")
        else:
            lines.append("  The prover could not prove it (it may still be true; make the step simpler or more explicit).")
    return "\n".join(lines) or (step.message or step.status)


def _counterexample(text: str, scope=()) -> str:
    """A counter-example as the model reads it: the parts of the invariant a run of the loop found false (Lean text
    after ``dynamic.PART``) in L_spec."""
    from FormalLLM.lean.dynamic import PART
    out = []
    for line in text.split("\n"):
        at = line.find(PART)
        out.append(line[:at + len(PART)] + _lspec(line[at + len(PART):], scope) if at >= 0 else line)
    return "\n".join(out)


def closed_statement(obligation) -> str:
    """The obligation with its context as hypotheses: ``forall inputs, assumptions ==> statement`` (as Lean text)."""
    if obligation.body is not None:
        return obligation.statement if obligation.statement not in ("Prop", "Nat") else obligation.body
    return f"∀ {obligation.binders}, {obligation.statement}" if obligation.binders.strip() else obligation.statement


#: (pattern in the parser's message, hint): spellings from other languages
SYNTAX_HINTS = [
    (r"'\?'(?!\w)", "A conditional is written `a if c else b` (or `if c then a else b`), not `c ? a : b`."),
    (r"'s\.t\.?'|'such'", "Write `exists j: j < i and ...`, not `s.t.`."),
    (r"trailing '='", "Equality is `==` (`=` only appears in `let x = v; ...`)."),
    (r"'where'", "Put the condition in the body: `forall x in l: cond ==> ...`."),
]

#: (pattern in Lean's error, hint): the usual reasons a type-correct-looking step is not
TYPE_HINTS = [
    (r"expected to have type\s+prop|HAdd \S+ \S+ prop|HSub \S+ \S+ prop|HMul \S+ \S+ prop",
     "A value is written where a statement (true or false) is expected. A bind's `prop` is a statement about its "
     "variable (`x == ...`); to give the value itself, write `\"value\": ...` instead of `prop`."),
    (r"HAdd (str|\(?list)", "Strings and lists are joined with `++`, not `+`."),
    (r"GetElem\?? \(?list[^,]*\)? int", "A list index is a `nat`: convert an `int` with `to_nat(i)`."),
    (r"Inhabited", "This type has no default value, so `l[i]` cannot be used on its lists: use `l[i]?` (an option)."),
    (r"GetElem\?? str ", "A `str` is not indexed directly: index its characters, `list(s)[i]`."),
    (r"Unknown identifier `(\w+)\.", "`{0}` is not defined at this step: only the goal's inputs, its assumptions and "
                                     "the variables this step introduces can be used."),
    (r"Decidable \(∃|Decidable \(exists",
     "An `exists` over all numbers cannot be computed, and the program must run. Search a bounded range instead, "
     "e.g. `range(n + 1).any(lambda m: ...)`, or use a loop."),
    (r"Function expected at\s+(\w+)\b", "`{0}` is a value here, not a function: a variable of the goal named `{0}` "
                                         "hides the library name (write the library function as in Lean, e.g. "
                                         "`String.mk(...)`), or the call has too many arguments."),
]


def hints(message: str, table) -> str:
    """The hints whose pattern occurs in ``message``; ``{0}`` in a hint is the pattern's first group."""
    import re
    found = []
    for pattern, hint in table:
        m = re.search(pattern, message)
        if m:
            found.append(hint.format(*m.groups()))
    return "".join(f"\n  Hint: {h}" for h in found)


def unreadable(error: Exception) -> str:
    if isinstance(error, steps.StepError):
        return f"Your answer could not be read. In `{error.field}`: {error.message}" + hints(error.message, SYNTAX_HINTS)
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
