"""Teaching material for each refinement law, and the instantiated proof condition.

The paper's prompt (section 8.2) says "all the rules are included in the
context" and that the system "actively constructs prompts that include logical
formulae representing the specifications" -- the *condition* the model's answer
must satisfy is derived from the chosen law and the current specification
(Algorithm 1, ``condition <- Refine4LLM(spec, law)``) and shown to the model
before it writes anything. The previous prompts carried a one-line blurb per law
and spelled out an obligation for only two of ten.

A :class:`LawCard` holds what is true of a law *in general*: its rule, what each
parameter means, when it helps, and a worked example from a problem that is
**not** in the benchmark (a test enforces that, so the examples cannot leak
answers). :func:`condition_text` produces what is true of the law *for this
specification*, using the same substitution the engine itself uses.

Nothing here names a benchmark problem or a problem family; a test scans every
generated prompt for that.
"""

import os
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from FormalLLM.llm import spec_render as sr
from FormalLLM.lspec.ast import Variable
from FormalLLM.lspec.substitution import get_free_vars, substitute
from FormalLLM.refinement.frame import frame_names, rigid_conjuncts


@dataclass(frozen=True)
class LawCard:
    name: str
    title: str
    rule: str
    parameters: Tuple[Tuple[str, str], ...]     # (key, meaning)
    use_when: str
    example_spec: Optional[str] = None          # L_spec text, for the tests
    example_story: Optional[str] = None         # one-line description for the prompt
    example_parameters: Optional[Dict[str, str]] = None


CARDS: Dict[str, LawCard] = {c.name: c for c in (
    LawCard(
        name="assignment",
        title="finish with one assignment",
        rule="x : [P, Q]  refines to  x := E     provided  P implies Q[x := E]",
        parameters=(("variable", "the frame variable to assign"),
                    ("expr", "E, an expression over the constants and frame variables")),
        use_when=("Q can be made true by setting one variable directly: Q pins a variable to "
                  "a formula of the others, or a simple constant already satisfies Q. If Q "
                  "constrains the variable only through inequalities that no single formula "
                  "satisfies for every input, one assignment will not do; split the problem "
                  "or use a loop."),
        example_story="a difference d = a - b of two numbers with a >= b",
        example_spec=("Frame: d:int.\n"
                      "Precondition: (a:int)(b:int) := a >= b.\n"
                      "Postcondition: (a:int)(b:int) := d >= 0 /\\ d + b = a."),
        example_parameters={"variable": "d", "expr": "a - b"},
    ),
    LawCard(
        name="skip",
        title="do nothing",
        rule="x : [P, Q]  refines to  skip     provided  P implies Q",
        parameters=(),
        use_when="the precondition already guarantees the postcondition.",
    ),
    LawCard(
        name="initialized_skip",
        title="do nothing, keeping every variable's old value",
        rule=("x : [P, Q]  refines to  skip     provided  P and (v = v0 for every frame variable v) "
              "implies Q"),
        parameters=(),
        use_when=("Q is satisfied as long as every frame variable keeps the value it had on entry."),
    ),
    LawCard(
        name="sequential",
        title="split into two stages",
        rule="x : [P, Q]  refines to  x : [P, R] ; x : [R, Q]     for any formula R",
        parameters=(("intermediate", "R, the state reached between the two stages"),),
        use_when=("the task has stages: first reach an intermediate state R, then reach Q from R. "
                  "A good R is the result of one stage: a conjunct of Q that an easy initialisation "
                  "establishes, or a state from which what remains is a single loop. R becomes the "
                  "postcondition of the first half and the precondition of the second half, so it "
                  "must contain every fact the second half will need (ranges, signs, relations "
                  "between variables; if the second half is a loop, R is its invariant). The facts "
                  "P states about constants are added for you. R must differ from P and from Q."),
        example_story="producing two outputs one after the other",
        example_spec=("Frame: q:int, r:int.\n"
                      "Precondition: (n:int) := n >= 0.\n"
                      "Postcondition: (n:int) := q = n + 1 /\\ r = 2 * n."),
        example_parameters={"intermediate": "q = n + 1"},
    ),
    LawCard(
        name="flexible_sequential",
        title="split into two stages with independent conditions",
        rule=("x : [P, Q]  refines to  x : [A, B] ; x : [C, D]     provided  P implies A, "
              "B implies C and D implies Q"),
        parameters=(("pre1", "A"), ("post1", "B"), ("pre2", "C"), ("post2", "D")),
        use_when=("a split in which the halves' conditions need not be exactly P, R, R, Q: "
                  "A may be weaker than P and D stronger than Q."),
        example_story="two stages that each get their own simplified condition",
        example_spec=("Frame: m:int, k:int.\n"
                      "Precondition: (n:int) := n >= 0.\n"
                      "Postcondition: (n:int) := k = 2 * n + 1."),
        example_parameters={"pre1": "n >= 0", "post1": "m = 2 * n",
                            "pre2": "m = 2 * n", "post2": "k = 2 * n + 1"},
    ),
    LawCard(
        name="alternation",
        title="split into two cases",
        rule=("x : [P, Q]  refines to  if G then x : [P and G, Q] else x : [P and not G, Q]"),
        parameters=(("guard", "G, a test on the state"),),
        use_when=("different inputs need different treatment, or one case makes Q easy. G should test the "
                  "inputs (names that never change), or a variable the precondition already constrains. "
                  "A test on a variable the program is still computing, whose starting value is arbitrary, "
                  "cannot tell cases of the problem apart and is refused."),
        example_story="a flag that records whether a reading reaches a threshold",
        example_spec=("Frame: s:int.\n"
                      "Precondition: (t:int) := true.\n"
                      "Postcondition: (t:int) := (t >= 10 /\\ s = 1) \\/ (t < 10 /\\ s = 0)."),
        example_parameters={"guard": "t >= 10"},
    ),
    LawCard(
        name="iteration",
        title="loop whose invariant is the precondition",
        rule=("x : [P, Q]  refines to  while G do x : [P and G and V = V0, P and V < V0]     "
              "provided  P and not G implies Q"),
        parameters=(("guard", "G, the loop condition"),
                    ("variant", "V, an expression that must get smaller on every iteration")),
        use_when=("P already holds on entry and is itself a good invariant (it stays true after "
                  "each iteration). If the loop needs a set-up step or a stronger invariant than P, "
                  "use sequential first or use initialised_iteration."),
    ),
    LawCard(
        name="initialised_iteration",
        title="set-up step followed by a loop with your own invariant",
        rule=("x : [P, Q]  refines to  x : [P, I] ; while G do x : [I and G and V = V0, I and V < V0]"
              "     provided  I and not G implies Q"),
        parameters=(("invariant", "I, true after the set-up and after every iteration"),
                    ("guard", "G, the loop condition"),
                    ("variant", "V, an expression that must get smaller on every iteration")),
        use_when=("the postcondition is reached by repeating a step: search, accumulate, scan, "
                  "approach a bound. It introduces the set-up step [P, I] and the loop together. "
                  "Follow the loop recipe."),
        example_story="a product built by repeated addition",
        example_spec=("Frame: r:int, i:int.\n"
                      "Precondition: (a:int)(b:int) := b >= 0.\n"
                      "Postcondition: (a:int)(b:int) := r = a * b."),
        example_parameters={"invariant": "r = a * i && 0 <= i && i <= b",
                            "guard": "i < b", "variant": "b - i"},
    ),
    LawCard(
        name="strengthen_post",
        title="aim at a stronger postcondition",
        rule="x : [P, Q]  refines to  x : [P, R]     provided  R implies Q",
        parameters=(("intermediate_post", "R, a formula that implies Q"),),
        use_when=("a more specific target R implies Q and is easier to reach, or R adds a constraint "
                  "that later steps need. It never makes the task easier by itself: the program must "
                  "then establish R. R must be strictly stronger than Q."),
        example_story="choosing one concrete witness for an inequality",
        example_spec=("Precondition: (n:int) := n >= 0.\n"
                      "Postcondition: (n:int) := y >= n."),
        example_parameters={"intermediate_post": "y = n + 1"},
    ),
    LawCard(
        name="weaken_pre",
        title="assume less",
        rule="x : [P, Q]  refines to  x : [R, Q]     provided  P implies R",
        parameters=(("intermediate_pre", "R, a formula implied by P"),),
        use_when=("to drop assumptions that are not needed, so that the specification matches a "
                  "simpler pattern. It never helps by itself: the program must then work under the "
                  "weaker assumption R. R must be strictly weaker than P."),
        example_story="forgetting a fact about a second input",
        example_spec=("Precondition: (n:int)(m:int) := n >= 5 /\\ m >= 0.\n"
                      "Postcondition: (n:int)(m:int) := y >= n."),
        example_parameters={"intermediate_pre": "n >= 5"},
    ),
)}

#: Presentation order; anything unlisted follows alphabetically.
LAW_ORDER = ["assignment", "skip", "initialized_skip", "sequential",
             "flexible_sequential", "alternation", "iteration", "initialised_iteration",
             "strengthen_post", "weaken_pre"]

LOOP_LAWS = ("iteration", "initialised_iteration")
MASSAGING_LAWS = ("strengthen_post", "weaken_pre")


def strict_variants() -> bool:
    """Whether the engine requires ``0 <= V`` as well as ``V < V0`` (see the loop laws)."""
    return os.environ.get("FORMALLLM_STRICT_VARIANT", "1") == "1"


def variant_rule() -> str:
    if strict_variants():
        return "V must stay >= 0 and be strictly smaller after every iteration"
    return "V must be strictly smaller after every iteration"


def ordered(available: Optional[List[str]] = None) -> List[str]:
    names = list(available) if available is not None else list(CARDS)
    first = [n for n in LAW_ORDER if n in names]
    rest = sorted(n for n in names if n not in LAW_ORDER)
    return [n for n in first + rest if n in CARDS]


# --- the general method, shared by the prompts ------------------------------

ROLE = (
    "You are an expert in Morgan's refinement calculus. You derive a correct program from a "
    "formal specification one refinement law at a time. An automatic theorem prover checks "
    "every step, so only logically sound choices are accepted; you cannot see the prover's "
    "work, only its verdicts."
)

NOTATION = (
    "A specification  x : [P, Q]  reads: starting in any state that satisfies the precondition P, "
    "change only the frame variables x so that the postcondition Q holds when the program stops. "
    "Names outside the frame are constants: they never change, so whatever P says about them stays "
    "true everywhere. A refinement law replaces a specification by a program or by simpler "
    "specifications; the law's side condition is proved automatically."
)

LANGUAGE = (
    "Expression language (use it for every formula you write):\n"
    "- numbers such as 3 or 0.5; booleans true and false\n"
    "- arithmetic + - * / and parentheses (for int operands / gives a whole number; for float "
    "operands it is exact)\n"
    "- comparisons < <= = > >= !=   (equality is a single =)\n"
    "- logic: && (and), || (or), ! (not). There is no implication operator: write 'A implies B' as !(A) || B.\n"
    "- quantifiers, only if the specification uses them, are written like the specification writes them: "
    "forall (k:int) formula   or   exists (k:int) formula  (binder in parentheses, then the formula; no colon, "
    "dot or comma). A quantifier reaches as far right as possible, so put it in parentheses when anything "
    "follows it: 0 <= i && (forall (k:int) !(k < i) || a[k] <= m)\n"
    "- array reading a[i]\n"
    "- v0 is the value variable v had before this step\n"
    "- there are NO function calls of any kind (no pow, floor, len, ...) and no if-then-else "
    "expressions: build every formula from the operators above.\n"
    "- only frame variables may be assigned; every other name is a fixed constant."
)

STRATEGY = (
    "How to choose the next step (a general method):\n"
    "1. If the system check says skip is valid, use skip.\n"
    "2. If one assignment could establish Q (Q pins a frame variable to a formula, or a simple "
    "constant already satisfies it), use assignment.\n"
    "3. If Q is reached by repeating a step (searching, accumulating, scanning, approaching a "
    "bound), design a loop with initialised_iteration, or use sequential and then iteration. Follow "
    "the loop recipe.\n"
    "4. If the task has distinct stages, use sequential with an intermediate assertion R that holds "
    "every fact the next stage needs.\n"
    "5. If different inputs need different treatment, use alternation on a test G.\n"
    "6. strengthen_post and weaken_pre only reshape the specification; they never make the task "
    "easier by themselves. Use them only if you can name the concrete fact they add or drop and why "
    "the next step needs it, and never apply one to the result of the other.\n"
    "Every step must make progress: the sub-specifications it produces must differ from the one you "
    "started with."
)

LOOP_RECIPE = (
    "Loop recipe (general):\n"
    "1. Look at Q. When it is a conjunction, one part A can usually be made true by a simple "
    "initial assignment, while another part B is what the loop must achieve.\n"
    "2. Invariant I: start from A and add every fact the loop body relies on, for instance the range "
    "or sign of each variable the body changes and the relations between loop variables and constants. "
    "I must be true after the set-up and be preserved by one iteration.\n"
    "3. Guard G: the negation of B, so that when the loop stops (I and not G) the postcondition Q holds.\n"
    "4. Variant V: an expression measuring how far the state is from satisfying B; " "{variant_rule}.\n"
    "5. The loop body is then usually a single assignment (or two in sequence) that moves a variable "
    "towards satisfying B."
)

REJECTION_NOTE = (
    "Reading a rejection: it lists values that satisfy the assumptions but violate the goal. Work out "
    "which fact those values break, then add or change exactly that fact in the parameters of the "
    "step that created the failing sub-goal (typically the invariant or the intermediate assertion), "
    "rather than re-wording the failing sub-goal itself."
)


def loop_recipe() -> str:
    return LOOP_RECIPE.replace("{variant_rule}", variant_rule())


# --- instantiated conditions ------------------------------------------------

def _hole_name(spec) -> str:
    taken = get_free_vars(spec.precondition.expr) | get_free_vars(spec.postcondition.expr)
    for candidate in ("E", "E_", "E__"):
        if candidate not in taken:
            return candidate
    return "E___"


def _frame_variable_names(spec) -> List[str]:
    return sorted(frame_names(spec.frame)) if spec.frame else []


def system_check_skip(spec) -> Tuple[str, str]:
    """Whether ``P implies Q`` already holds, decided by the prover.

    Returns ``(status, values)``: status is PROVED, FAILED or UNKNOWN, and for
    FAILED ``values`` are counterexample values written in the readable syntax.
    """
    from FormalLLM.refinement.frame import obligation_params
    from FormalLLM.verification.proof_obligations import ProofObligation
    from FormalLLM.verification.z3_backend import check_implication

    return check_implication(ProofObligation(
        assumptions=[spec.precondition.expr], goal=spec.postcondition.expr,
        params=obligation_params(spec)))


def condition_text(law: str, spec, brief: bool = False) -> str:
    """What the system will check for ``law`` on ``spec``, as concrete formulas.

    ``brief`` is for the law-selection turn, where the specification is already
    on the page: it states the shape of the check without repeating P and Q.
    """
    pre, post = spec.precondition.expr, spec.postcondition.expr
    lines: List[str] = []
    constants = [sr.render_expr(c) for c in rigid_conjuncts(pre, spec.frame)]

    if law == "assignment":
        hole = _hole_name(spec)
        lines.append(f"The system checks that P implies Q with the assigned variable v replaced by "
                     f"{hole} ({hole} is the formula you write). Written out:")
        if spec.frame:
            for target in _frame_variable_names(spec):
                lines.append(f"  if v is {target}, then {hole} must make all of these true:")
                lines.append(sr.bullets(substitute(post, target, Variable(hole)), indent="    "))
        else:
            lines.append("  (the specification declares no frame; Q is shown unchanged)")
            lines.append(sr.bullets(post, indent="    "))
    elif law in ("skip", "initialized_skip"):
        extra = " together with v = v0 for every frame variable v" if law == "initialized_skip" else ""
        lines.append(f"The system checks that P{extra} implies Q.")
    elif law == "sequential":
        lines.append("Two new specifications are created and refined next (no proof condition now):")
        lines.append("  first half   [ P , R ]")
        lines.append("  second half  [ R , Q ]")
        if constants:
            lines.append("  facts about constants added to R automatically: " + "; ".join(constants))
    elif law == "flexible_sequential":
        lines.append("The system checks: P implies A, B implies C, and D implies Q.")
    elif law == "alternation":
        lines.append("Two new specifications are created and refined next:")
        lines.append("  then-branch  [ P and G , Q ]")
        lines.append("  else-branch  [ P and not G , Q ]")
    elif law in LOOP_LAWS:
        inv = "P" if law == "iteration" else "I"
        exit_line = f"The system checks the exit condition: {inv} and not G implies Q."
        if brief:
            lines.append(exit_line)
        else:
            lines.append(exit_line + " Here Q is:")
            lines.append(sr.bullets(post, indent="    "))
            if law == "iteration":
                lines.append("and the invariant is P itself:")
                lines.append(sr.bullets(pre, indent="    "))
        lines.append("Then these specifications are refined next:")
        if law == "initialised_iteration":
            lines.append("  set-up       [ P , I ]")
        zero = " and 0 <= V" if strict_variants() else ""
        lines.append(f"  loop body    [ {inv} and G and V = V0 ,  {inv}{zero} and V < V0 ]"
                     "   (V0 is the value of V when the body starts)")
        if constants and law == "initialised_iteration":
            lines.append("  facts about constants added to I automatically: " + "; ".join(constants))
    elif law == "strengthen_post":
        lines.append("The system checks R implies Q, then refines [ P , R ].")
    elif law == "weaken_pre":
        lines.append("The system checks P implies R, then refines [ R , Q ].")
    return "\n".join(lines)


def card_text(law: str) -> str:
    """The general card for ``law``: rule, parameters, when to use it."""
    card = CARDS[law]
    out = [f"- {card.name}: {card.title}", f"    rule: {card.rule}"]
    if card.parameters:
        params = "; ".join(f'"{k}" = {meaning}' for k, meaning in card.parameters)
        out.append(f"    parameters: {params}")
    else:
        out.append("    parameters: none")
    out.append(f"    use when: {card.use_when}")
    if law in LOOP_LAWS:
        out.append(f"    termination: {variant_rule()}.")
    return "\n".join(out)


def example_text(law: str) -> str:
    """A worked parameter example from an unrelated problem."""
    import json
    card = CARDS[law]
    if not card.example_parameters:
        return ""
    return (f"Example (a different problem: {card.example_story}):\n"
            + "\n".join("  " + line for line in card.example_spec.splitlines())
            + "\n  reply: " + json.dumps({"parameters": card.example_parameters}))
