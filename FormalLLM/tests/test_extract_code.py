"""Turning a model's reply into a program: JSON-wrapped, fenced and bare replies.

Regression for a measurement bug: the hosted endpoint answers in a forced JSON object
(``{"code": "python\\n..."}``). The extractor used to know only Markdown fences, so it ran the raw
JSON as Python, got a SyntaxError for every problem, and the direct baseline scored 0 of 164.
These tests need no model and no evalplus.
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from benchmarks.datasets.humaneval import extract_code               # noqa: E402

FUNC = "def add(a, b):\n    return a + b\n"


def runs(code):
    ns = {}
    exec(compile(code, "<reply>", "exec"), ns)
    return ns["add"](2, 3)


def test_json_code_key_with_a_language_tag_line():
    # the shape of 147 of the 164 stored replies
    assert runs(extract_code(json.dumps({"code": "python\n" + FUNC}))) == 5


def test_json_with_a_fence_inside_the_value():
    assert runs(extract_code(json.dumps({"code": "```python\n" + FUNC + "```"}))) == 5


def test_json_python_key_and_chat_message_shapes():
    assert runs(extract_code(json.dumps({"python": FUNC}))) == 5
    assert runs(extract_code(json.dumps({"role": "assistant", "content": "```python\n" + FUNC + "```"}))) == 5


def test_json_with_two_string_keys_prefers_the_one_that_defines_a_function():
    reply = json.dumps({"code": "see below", "content": FUNC})
    assert runs(extract_code(reply)) == 5


def test_json_with_an_unknown_key_still_yields_its_string():
    assert runs(extract_code(json.dumps({"reply": FUNC}))) == 5


def test_plain_markdown_fence_and_bare_code_are_unchanged():
    assert runs(extract_code("Here you go:\n```python\n" + FUNC + "```\nDone.")) == 5
    assert extract_code(FUNC) == FUNC


def test_a_language_tag_line_is_dropped_but_code_starting_with_py_names_is_kept():
    assert extract_code("python\n" + FUNC) == FUNC
    keep = "python_version = 3\n" + FUNC
    assert extract_code(keep) == keep


def test_text_that_only_looks_like_json_is_returned_as_is():
    broken = '{"code": "def f(:'
    assert extract_code(broken) == broken
    assert extract_code("{1, 2}") == "{1, 2}"
