from typing import List
from FormalLLM.refinement.graph.node import RefinementNode
from FormalLLM.lspec import walk
from FormalLLM.lspec.ast import *
from FormalLLM.lpl.ast import *
from FormalLLM.llm import law_cards as lc
from FormalLLM.llm import spec_render as sr

def to_string(node: ASTNode, compact: bool = False) -> str:
    if isinstance(node, BinaryOp):
        # Add parentheses for safety
        return f"({to_string(node.left)} {node.op} {to_string(node.right)})"
    elif isinstance(node, UnaryOp):
        return f"({node.op}{to_string(node.expr)})"
    elif isinstance(node, Variable):
        return node.name
    elif isinstance(node, Const):
        return node.name
    elif isinstance(node, Number) or isinstance(node, BooleanConst):
        return str(node.value)
    elif isinstance(node, Definition):
        params = "".join(f"({p.name}:{p.type_.__class__.__name__.replace('Type', '').lower()})" for p in node.params)
        return f"{params} := {to_string(node.expr)}"
    elif isinstance(node, QuantifiedExpr):
        params = "".join(f"({p.name}:{p.type_.__class__.__name__.replace('Type', '').lower()})" for p in node.params)
        return f"({node.quantifier} {params} {to_string(node.expr)})"
    elif isinstance(node, VariablePreviousState):
        return f"{node.name}0"
    elif isinstance(node, ArraySelect):
        return f"{node.array}[{to_string(node.index)}]"
    elif isinstance(node, ArraySlice):
        return f"{node.array}[{to_string(node.start)}:{to_string(node.end)}]"
    elif isinstance(node, Spec):
        if compact:
            return f"[{to_string(node.precondition.expr)}, {to_string(node.postcondition.expr)}]"
        else:
            return f"Precondition: {to_string(node.precondition)}\nPostcondition: {to_string(node.postcondition)}"
    elif isinstance(node, Assignment):
        return f"{node.variable} := {to_string(node.expr)}"
    elif isinstance(node, Skip):
        return "skip"
    elif isinstance(node, SequentialComposition):
        return f"{to_string(node.first, compact=True)} ;\n{to_string(node.second, compact=True)}"
    elif isinstance(node, IfElse):
        return f"if {to_string(node.guard)}:\n  {to_string(node.then_branch, compact=True)}\nelse:\n  {to_string(node.else_branch, compact=True)}"
    elif isinstance(node, While):
        return f"while {to_string(node.guard)}:\n  {to_string(node.body, compact=True)}"
    # No silent fallback: `str(node)` rendered an unhandled node as its
    # dataclass repr, which then travelled into the LLM prompt and into
    # `spec_key`, where the progress guard compares specifications as strings.
    # Fail loudly instead.
    raise walk.UnknownNodeError(node)


# One line per law: what it does and the keys it takes. The full teaching
# material (rule, when to use it, worked example, instantiated condition) lives
# in law_cards; this table is the compact index and is what the law contract
# test checks every registered law against.
LAW_DESCRIPTIONS = {
    name: (f'{card.title} -- parameters: '
           + (", ".join(f'"{key}"' for key, _ in card.parameters) if card.parameters else "none")
           + f' -- {card.rule}')
    for name, card in lc.CARDS.items()
}

# Presentation order; anything unlisted is appended alphabetically.
LAW_ORDER = lc.LAW_ORDER

SYNTAX_HELP = lc.LANGUAGE


# --- sections ---------------------------------------------------------------

def _spec_section(spec) -> str:
    return "## The specification to refine\n" + sr.render_spec(spec)


def _system_check(spec) -> str:
    """Facts the prover can settle now, so the model need not guess them."""
    try:
        status, values = lc.system_check_skip(spec)
    except Exception:           # a check that cannot run must never break a prompt
        status, values = "UNKNOWN", ""
    if status == "PROVED":
        return "System check: P already implies Q, so skip is valid."
    if status == "FAILED":
        suffix = f" (for example, {values} satisfy P but not Q)" if values else ""
        return f"System check: P does NOT imply Q, so skip is not valid{suffix}."
    return "System check: whether skip is valid could not be decided."


def _laws_section(spec, available_laws: List[str]) -> str:
    blocks = []
    for name in lc.ordered(available_laws):
        text = lc.card_text(name)
        cond = lc.condition_text(name, spec, brief=True)
        if cond:
            text += "\n    for this specification:\n" + "\n".join("      " + l for l in cond.splitlines())
        blocks.append(text)
    return "## Available laws\n" + "\n".join(blocks)


def _blacklist_line(blacklisted_laws: List[str]) -> str:
    if not blacklisted_laws:
        return ""
    return (f"\nThe following laws have been exhausted and must NOT be used: "
            f"{', '.join(blacklisted_laws)}\n")


def _history(history_context: str) -> str:
    return f"\n{history_context}\n" if history_context else ""


def _available(available_laws):
    return list(available_laws) if available_laws is not None else list(lc.CARDS)


# --- prompts -----------------------------------------------------------------

def generate_state_prompt(node: RefinementNode,
                          blacklisted_laws: List[str] = None,
                          history_context: str = "",
                          available_laws: List[str] = None) -> str:
    """One call that picks the law *and* writes its parameters (single-turn mode).

    `available_laws` restricts the advertised laws to those the engine has
    actually registered: advertising a law the engine cannot apply only wastes
    retries.
    """
    spec = node.specification
    available = _available(available_laws)
    parts = [
        lc.ROLE,
        lc.NOTATION,
        lc.LANGUAGE,
        _spec_section(spec),
        _system_check(spec),
        _laws_section(spec, available),
        lc.STRATEGY,
        lc.loop_recipe(),
        "## Reply format\n"
        "Reply with one JSON object and nothing else:\n"
        '{"law": "<one of the law names above>", "parameters": {<exactly the keys that law lists>}, '
        '"rationale": "<one or two sentences>"}\n'
        "Use the parameter keys exactly as listed for the law, with formulas as strings.",
    ]
    prompt = "\n\n".join(parts) + "\n"
    prompt += _blacklist_line(blacklisted_laws or [])
    if history_context:
        prompt += _history(history_context) + "\n" + lc.REJECTION_NOTE + "\n"
    return prompt


def generate_law_selection_prompt(node: RefinementNode,
                                  blacklisted_laws: List[str] = None,
                                  available_laws: List[str] = None,
                                  history_context: str = "") -> str:
    """Turn 1: choose a law. Parameters are written in turn 2."""
    spec = node.specification
    available = _available(available_laws)
    parts = [
        lc.ROLE,
        lc.NOTATION,
        lc.LANGUAGE,
        _spec_section(spec),
        _system_check(spec),
        _laws_section(spec, available),
        lc.STRATEGY,
        lc.loop_recipe(),
        "## Reply format\n"
        "Choose the law only; its parameters are requested next. Reply with one JSON object and "
        "nothing else:\n"
        '{"law": "<one of the law names above>", "rationale": "<one or two sentences>"}',
    ]
    prompt = "\n\n".join(parts) + "\n"
    prompt += _blacklist_line(blacklisted_laws or [])
    if history_context:
        prompt += _history(history_context) + "\n" + lc.REJECTION_NOTE + "\n"
    return prompt


def generate_parameter_synthesis_prompt(node: RefinementNode, law: str, history_context: str = "") -> str:
    """Turn 2: write the parameters of the chosen law."""
    spec = node.specification
    card = lc.CARDS.get(law)

    if history_context:
        header = f"[retry — law: {law}, prior attempts failed (see feedback below)]\n\n"
    else:
        header = f"[fresh attempt — law: {law}]\n\n"

    parts = [lc.ROLE, lc.NOTATION, lc.LANGUAGE, _spec_section(spec)]

    if card is not None:
        parts.append(f"## The law you chose: {law}\n" + lc.card_text(law))
        cond = lc.condition_text(law, spec)
        if cond:
            parts.append("## What the system will check for this specification\n" + cond)
        if law in lc.LOOP_LAWS:
            parts.append(lc.loop_recipe())
        example = lc.example_text(law)
        if example:
            parts.append(example)
        keys = ", ".join(f'"{k}"' for k, _ in card.parameters)
    else:
        keys = ""

    parts.append(
        "## Reply format\n"
        "Reply with one JSON object and nothing else:\n"
        '{"parameters": {' + (keys and "<one entry per key: " + keys + ">") + '}, '
        '"rationale": "<one or two sentences>"}\n'
        "Use exactly the parameter keys listed for the law, with each formula written as a string."
        + (" This law takes no parameters, so send an empty object." if card is not None and not card.parameters else "")
    )

    prompt = header + "\n\n".join(parts) + "\n"
    if history_context:
        prompt += _history(history_context) + "\n" + lc.REJECTION_NOTE + "\n"
        prompt += "\nReview the failed attempts above and choose DIFFERENT, valid parameters.\n"
    return prompt
