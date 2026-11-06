"""What the model reads when it writes L_spec: the task's specification, the goal, and the laws, for both workflows.

* ``joint``: one model chooses the law and writes it (``joint_prompt``; the reply is a whole step, ``steps.FIELDS``).
* ``split``: a selector names the law and says in a sentence how it will be used (``selector_prompt``), then an applier
  writes that law's fields (``applier_prompt``).

The protocol is the paper's: the model never writes proofs or lemmas; the prover proves every obligation, and a step it
cannot prove is refused with the reason (``feedback.py``). Nothing here depends on the task beyond its own text."""
import json
from typing import List, Optional

from FormalLLM.dsl import cheatsheet, defs, steps

LAWS = """A goal asks for a value with a given type and property, in a context of inputs and assumptions. A step is one
refinement law, written as a JSON object whose expressions are L_spec:

1. term: the value is an expression. The prover must show the property for it from the assumptions.
   {"law": "term", "expr": "<expression>"}
2. cases: split on a condition; one new goal assumes it, the other assumes its negation. Use it when the answer
   differs by case.
   {"law": "cases", "cond": "<condition>"}
3. bind: first find a value `var` of type `type` with property `prop`, then continue with it (and `prop`) available.
   Use it to compute something once and reuse it. `prop` is a statement about `var` (true or false), not a value;
   to name a known value write "value" instead of "prop" (it means `var == value`).
   {"law": "bind", "var": "<new name>", "type": "<type>", "prop": "<property of var>"}
   {"law": "bind", "var": "m", "type": "rat", "value": "sum(l) / (len(l) as rat)"}
4. loop: state variables with their types and initial values; repeat while `guard`. `invariant` must hold at the start,
   be kept by every iteration, and, together with `not guard`, imply the goal's property for `result`. `variant` is a
   nat that every iteration makes smaller. The new goal is the loop body: find the next state (usually a `term` that is
   a tuple).
   {"law": "loop", "state": [["i", "nat", "0"], ["acc", "int", "0"]], "invariant": "<property of the state>",
    "guard": "<condition>", "variant": "<nat expression>", "result": "<expression over the state>"}

Every expression is a JSON string, including numbers and booleans ("0", "False", "[]"). New names (bind variable,
state variables) must not already be in scope. You never write proofs: if the prover cannot
prove a step it is refused with the reason, and you write a different one."""

EXAMPLE = """Example. Goal: inputs n: nat; find result: nat such that 2 * result == n * (n + 1).
{"law": "loop", "state": [["i", "nat", "0"], ["s", "nat", "0"]], "invariant": "s * 2 == i * (i + 1) and i <= n",
 "guard": "i < n", "variant": "n - i", "result": "s"}
The loop body's goal: find (i_next, s_next) such that s_next * 2 == i_next * (i_next + 1) and i_next <= n and
n - i_next < n - i. Answer:
{"law": "term", "expr": "(i + 1, s + (i + 1))"}"""


def specification(prelude: str) -> str:
    """The task's definitions in L_spec (a command L_spec does not cover is shown as Lean, marked)."""
    return "\n\n".join(defs.show_lspec(item) for item in defs.read(prelude)
                       if not (isinstance(item, defs.Verbatim)
                               and item.source.split()[0] in ("open", "set_option", "namespace", "end", "section")))


def _context(task, goal_text: str, failures: List[str]) -> List[str]:
    parts = [f"Task: {task.name}", task.description[:1500].strip(), "",
             "Specification (L_spec):", specification(task.prelude)[-3000:], "",
             "Goal:", goal_text]
    if failures:
        parts += ["", "Earlier attempts on this goal were refused:"] + failures[-3:]
    return parts


def joint_prompt(task, goal_text: str, failures: List[str] = ()) -> str:
    """Workflow ``joint``: choose a law and write it."""
    return "\n".join([LAWS, "", EXAMPLE, "", cheatsheet.sheet(), ""] + _context(task, goal_text, list(failures))
                     + ["", "Your step (one JSON object, nothing else):"])


def selector_prompt(task, goal_text: str, failures: List[str] = ()) -> str:
    """Workflow ``split``, first call: which law, and how (one sentence). No L_spec is written here."""
    return "\n".join([LAWS, "", EXAMPLE, ""] + _context(task, goal_text, list(failures)) + [
        "", 'Choose the law for this goal. Answer {"law": "<term|cases|bind|loop>", "plan": "<one sentence: what the '
        'value, condition, intermediate value or loop is>"} and nothing else.'])


def applier_prompt(task, goal_text: str, law: str, plan: Optional[str] = None, failures: List[str] = ()) -> str:
    """Workflow ``split``, second call: write the chosen law's fields in L_spec."""
    fields = ", ".join(f'"{f}"' for f, _ in steps.fields_for(law))
    return "\n".join([LAWS, "", EXAMPLE, "", cheatsheet.sheet(), ""] + _context(task, goal_text, list(failures)) + [
        "", f"The law for this goal is `{law}`." + (f" Plan: {plan}" if plan else ""),
        f'Write it: one JSON object {{"law": "{law}", {fields}}} with every expression in L_spec, nothing else.'])


def parse_reply(reply: str) -> dict:
    """The JSON object in a reply (code fences and words around it tolerated); ``StepError`` if there is none."""
    from FormalLLM.lean.agent import extract_json
    found = extract_json(reply)
    if found is None:
        raise steps.StepError("reply", "no JSON object found; answer with one JSON object")
    return found


def show_step(step: dict) -> str:
    return json.dumps(step, ensure_ascii=False)
