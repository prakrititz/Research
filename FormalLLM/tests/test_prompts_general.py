"""The prompts must be general: no benchmark problem may be named or hinted at.

The professor's comment on the earlier prompts was that they were "not very
detailed and oriented towards this particular problem". This file makes the
second half of that a regression test: the static text of every prompt is
scanned for words that belong to the benchmark's problems, and every worked
example in the prompts is checked to be (a) not a benchmark problem and (b) a
refinement the engine really accepts, so the examples cannot teach a mistake.
"""
import json
import os
import re
import sys

import pytest

from FormalLLM.llm import law_cards as lc
from FormalLLM.llm import prompts as P
from FormalLLM.llm.parser import parse_expr, parse_parameters_response, parse_law_response
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.engine import RefinementEngine
from FormalLLM.refinement.graph.graph import RefinementGraph

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))
from cases import CASES  # noqa: E402

# A neutral specification that shares no wording with any benchmark case.
NEUTRAL = (
    "Frame: w:int.\n"
    "Precondition: (k:int)(m:int) := k >= 1 /\\ m >= 2.\n"
    "Postcondition: (k:int)(m:int) := w >= k /\\ w <= m."
)

# Words that name the benchmark's problems or problem families.
FORBIDDEN = ["sqrt", "square", "root", "quotient", "remainder", "division", "factorial",
             "absolute", "counting", "intdiv", "maximum", "newton", "bisect", "binary search"]


def node_for(spec_text):
    graph = RefinementGraph(parse_spec(spec_text))
    return graph.nodes[graph.root_id]


def all_static_prompts():
    node = node_for(NEUTRAL)
    laws = list(lc.CARDS)
    yield "turn1", P.generate_law_selection_prompt(node, [], laws)
    yield "single", P.generate_state_prompt(node, [], "", laws)
    for law in laws:
        yield f"turn2:{law}", P.generate_parameter_synthesis_prompt(node, law)


_STATIC = list(all_static_prompts())


@pytest.mark.parametrize("label,text", _STATIC, ids=[label for label, _ in _STATIC])
def test_no_benchmark_vocabulary_in_any_prompt(label, text):
    lowered = text.lower()
    for word in FORBIDDEN:
        assert word not in lowered, f"{label} mentions {word!r}"


@pytest.mark.parametrize("case", CASES, ids=[c["id"] for c in CASES])
def test_prompts_for_every_benchmark_spec_add_nothing_problem_specific(case):
    """Whatever differs between two specs' prompts must come from the spec itself."""
    spec_text = case["spec"]
    node = node_for(spec_text)
    prompt = P.generate_law_selection_prompt(node, [], list(lc.CARDS))
    neutral = P.generate_law_selection_prompt(node_for(NEUTRAL), [], list(lc.CARDS))
    # Strip each prompt's own specification section and condition lines; what is left
    # (the teaching text) must be identical for every problem.
    def teaching(text):
        text = re.sub(r"## The specification to refine.*?## Available laws", "", text, flags=re.S)
        text = re.sub(r"System check:.*", "", text)
        text = re.sub(r"    for this specification:.*?(?=\n- |\n\nHow to choose)", "", text, flags=re.S)
        return text
    assert teaching(prompt) == teaching(neutral)


def test_fresh_and_retry_markers_and_forbidden_strings():
    node = node_for(NEUTRAL)
    fresh = P.generate_parameter_synthesis_prompt(node, "skip")
    retry = P.generate_parameter_synthesis_prompt(node, "skip", history_context="Previous failed attempts:\n- x")
    assert fresh.startswith("[fresh attempt")
    assert retry.startswith("[retry")
    for text in (fresh, retry):
        assert "50" not in text.replace("2500", ""), "digits '50' would collide with a feedback test"
    assert "Counterexample" not in fresh


def test_the_blacklist_phrase_is_kept():
    node = node_for(NEUTRAL)
    text = P.generate_law_selection_prompt(node, ["assignment"], list(lc.CARDS))
    assert "have been exhausted and must NOT be used: assignment" in text


# --- the worked examples -----------------------------------------------------

def normalised(spec_text):
    return re.sub(r"\s+", "", spec_text)


@pytest.mark.parametrize("law", [n for n, c in lc.CARDS.items() if c.example_parameters])
def test_example_is_not_a_benchmark_problem(law):
    example = normalised(lc.CARDS[law].example_spec)
    for case in CASES:
        assert example != normalised(case["spec"]), f"{law}'s example is benchmark case {case['id']}"


@pytest.mark.parametrize("law", [n for n, c in lc.CARDS.items() if c.example_parameters])
def test_example_is_a_refinement_the_engine_accepts(law):
    """A wrong example would teach the model a mistake with full confidence."""
    card = lc.CARDS[law]
    spec = parse_spec(card.example_spec)
    params = parse_parameters_response(json.dumps({"parameters": card.example_parameters}), law)
    result = RefinementEngine().apply(spec, law, params)     # raises if any obligation fails
    assert result.program is not None or result.sub_specs


@pytest.mark.parametrize("law", [n for n, c in lc.CARDS.items() if c.example_parameters])
def test_the_example_reply_parses_with_the_real_parser(law):
    text = lc.example_text(law)
    reply = text.split("reply: ", 1)[1]
    assert parse_parameters_response(reply, law)


def test_example_loop_body_is_itself_refinable():
    """The loop example is only worth showing if its body really is one or two assignments."""
    card = lc.CARDS["initialised_iteration"]
    spec = parse_spec(card.example_spec)
    engine = RefinementEngine()
    result = engine.apply(spec, "initialised_iteration",
                          parse_parameters_response(json.dumps({"parameters": card.example_parameters}),
                                                    "initialised_iteration"))
    roles = result.by_role()
    # set-up: r := 0 ; i := 0   via an intermediate
    setup = engine.apply(roles["init"], "sequential", {"intermediate": parse_expr("r = 0")})
    engine.apply(setup.sub_specs[0], "assignment", {"variable": "r", "expr": parse_expr("0")})
    engine.apply(setup.sub_specs[1], "assignment", {"variable": "i", "expr": parse_expr("0")})
    # body: r := r + a ; i := i + 1
    body = engine.apply(roles["body"], "sequential",
                        {"intermediate": parse_expr("r = a * (i + 1) && 0 <= i && i < b && b - i = V0")})
    engine.apply(body.sub_specs[0], "assignment", {"variable": "r", "expr": parse_expr("r + a")})
    engine.apply(body.sub_specs[1], "assignment", {"variable": "i", "expr": parse_expr("i + 1")})
