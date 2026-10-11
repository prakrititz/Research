"""Does a test on this variable mean anything here?

In ``x : [P, Q]`` the variable ``x`` is the one the program computes. Unless the precondition
constrains it, or the postcondition refers to its earlier value (``x0``), whatever ``x`` happens
to hold when the step starts is *arbitrary*, and a program that behaves differently for
different arbitrary values is solving a problem nobody posed.

Measured on the paper's square-root example: a run whose first move was ``if x*x <= N then ... else
...`` split the problem on the leftover value of the answer variable. The else-branch ("x is too
big to begin with") needed a different program, and about twenty LLM calls went into it before the
budget ran out. A test on the inputs (``N``, ``e``) would have been fine; the test on ``x`` was
legal but could never help.

:func:`pointless_test_variables` names the frame variables a guard mentions whose starting value is
arbitrary, so the engine can refuse the split with that explanation.
"""
import re
from typing import List

from FormalLLM.lspec.substitution import get_free_vars
from FormalLLM.refinement.frame import frame_names
from FormalLLM.refinement.vocabulary import previous_state_names, vocabulary


def entry_value_matters(spec, name: str) -> bool:
    """True if the precondition constrains ``name`` or the postcondition refers to its earlier value."""
    if name in get_free_vars(spec.precondition.expr):
        return True
    return name in previous_state_names(spec.postcondition.expr)


def pointless_test_variables(spec, guard) -> List[str]:
    """Frame variables mentioned in ``guard`` whose value on entry is arbitrary."""
    frame = frame_names(spec.frame)
    if not frame or guard is None:
        return []
    return sorted(v for v in get_free_vars(guard) & frame if not entry_value_matters(spec, v))


def pointless_test_message(spec, names: List[str]) -> str:
    inputs = sorted(n for n in vocabulary(spec) - frame_names(spec.frame))
    shown = ", ".join(names)
    plural = len(names) > 1
    return (f"The test mentions {shown}, but the value {'they have' if plural else shown + ' has'} when this "
            f"step starts is arbitrary: the precondition says nothing about {'them' if plural else 'it'} and the "
            f"postcondition does not refer to {'their' if plural else 'its'} earlier value, so a test on "
            f"{'them' if plural else 'it'} cannot tell the cases of this problem apart. Test the names that "
            f"never change ({', '.join(inputs) or 'none here'}) instead, or choose another law.")


def has_quantifier(node) -> bool:
    """Does the formula contain ``exists`` or ``forall``?"""
    from FormalLLM.lspec import walk
    from FormalLLM.lspec.ast import QuantifiedExpr
    return isinstance(node, QuantifiedExpr) or any(has_quantifier(child) for child in walk.children(node))


def unexecutable_guard_message(guard) -> str:
    """Why a guard with a quantifier cannot be used, or ``""`` if it is fine.

    A guard becomes the test of an ``if`` or a ``while`` in the finished program. The specification
    language may quantify over a range; the program language has no such test, so a proved
    derivation containing one cannot be run. Measured on the HumanEval pilot: ``is prime`` was
    "derived" as ``if exists k ...: ... else: ...``, which is correct and cannot be executed (the
    run crashed when the program was turned into Python).
    """
    if guard is None or not has_quantifier(guard):
        return ""
    return ("The guard uses a quantifier (exists/forall). A guard becomes the test of an if or while in the "
            "finished program, and a program can only evaluate tests made of numbers, names, array reads, "
            "arithmetic, comparisons and && || !. To search over a range, use a loop whose invariant "
            "records what has been checked so far, and keep the quantifier in the invariant, not the guard.")


_PROOF_ONLY = re.compile(r"^V\d+$")


def proof_only_names(node) -> List[str]:
    """Names in ``node`` that exist only in the proof, never in the running program.

    ``V0``, ``V1``, ... are the value of a loop's measure when an iteration starts, and ``x0`` is the value
    ``x`` had when the specification started. Both are logical constants the laws introduce; no variable
    of the program holds them. Measured on the HumanEval pilot (v8): a loop body was refined with
    ``if r = V0 then r := r - 1 else skip``. The precondition makes ``r = V0`` true, so the step is
    *valid*, but the emitted program read ``V0`` and stopped with ``NameError`` on every test.
    """
    from FormalLLM.lspec import walk
    from FormalLLM.lspec.ast import Const, Variable, VariablePreviousState
    found = []

    def visit(n):
        if isinstance(n, VariablePreviousState):
            found.append(f"{n.name}0")
        elif isinstance(n, (Variable, Const)) and _PROOF_ONLY.match(n.name):
            found.append(n.name)
        for child in walk.children(n):
            visit(child)

    if node is not None:
        visit(node)
    return sorted(set(found))


def proof_only_message(names: List[str], what: str) -> str:
    shown = ", ".join(names)
    return (f"The {what} uses {shown}, which exists only in the proof (V0 is the loop measure's value when the "
            f"iteration started; x0 is x's value when the specification started). The finished program has no "
            f"variable holding it, so it cannot test or compute with it. Use the program's own variables and the "
            f"constants instead.")
