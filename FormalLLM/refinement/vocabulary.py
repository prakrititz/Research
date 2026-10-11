"""Which names may a formula written for this specification use?

A refinement step's formulas (an invariant, an intermediate assertion, a guard) can only
talk about what the specification talks about: its frame variables, its constants and the
loop bookkeeping names (``V0``, ``V1`` ...) that enclosing loops introduced. A language
model sometimes names a quantity it has just computed -- ``V = N - (x+e)*(x+e)`` -- and
uses ``V`` as if it were a variable. The prover then treats ``V`` as an arbitrary unknown
constant, so the step is judged against a statement the model did not mean, and the
rejection that follows ("N = 1, V = 0 ...") never says that ``V`` was the mistake.

Measured on the paper's square-root example: one failed run proposed four loops in a row
whose formulas used an undefined ``V`` and ``D``.
"""

from typing import Dict, List, Set

from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import ASTNode, VariablePreviousState
from FormalLLM.lspec.substitution import get_free_vars
from FormalLLM.refinement.frame import frame_names


def vocabulary(spec) -> Set[str]:
    """Every name the specification itself uses."""
    names = set(get_free_vars(spec.precondition.expr)) | set(get_free_vars(spec.postcondition.expr))
    names |= {p.name for p in list(spec.precondition.params) + list(spec.postcondition.params)}
    names |= frame_names(spec.frame)
    return names


def previous_state_names(node) -> Set[str]:
    """Names written with a trailing 0 (`x0`, `V0`), which the parser reads as "value before the step"."""
    found = {node.name} if isinstance(node, VariablePreviousState) else set()
    for child in walk.children(node):
        found |= previous_state_names(child)
    return found


def unknown_names(spec, parameters: Dict[str, object]) -> List[str]:
    """Names used in the formulas of ``parameters`` that ``spec`` does not define, sorted.

    ``x0`` is the value ``x`` had before the step, so it is fine for any name the specification
    has; ``V0`` is also fine when the specification mentions the loop bookkeeping name ``V0``
    itself (the parser reads that as the previous state of ``V``).
    """
    allowed = vocabulary(spec)
    found: Set[str] = set()
    for value in (parameters or {}).values():
        if not isinstance(value, ASTNode):
            continue
        found |= set(get_free_vars(value)) - allowed
        for base in previous_state_names(value):
            if base not in allowed and (base + "0") not in allowed:
                found.add(base + "0")
    return sorted(found)


def describe_vocabulary(spec) -> str:
    """One line a reader can check a formula against."""
    frame = sorted(frame_names(spec.frame))
    others = sorted(vocabulary(spec) - set(frame))
    parts = []
    if frame:
        parts.append("frame variable" + ("s" if len(frame) > 1 else "") + " " + ", ".join(frame))
    if others:
        parts.append("constants " + ", ".join(others))
    return "; ".join(parts) if parts else "(none)"


def unknown_name_message(spec, names: List[str]) -> str:
    plural = len(names) > 1
    return (f"Your formula uses the name{'s' if plural else ''} {', '.join(names)}, which this "
            f"specification does not define. A formula may only use the names of the specification: "
            f"{describe_vocabulary(spec)}. Write the quantity out in full instead of giving it a name "
            f"(there are no new variables).")
