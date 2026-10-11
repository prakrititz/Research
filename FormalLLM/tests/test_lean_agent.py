"""The model-driven loop around the Lean engine, with a scripted stand-in for the model (no network)."""
import json

import pytest

from benchmarks.datasets.lean_taskfile import write_task
from FormalLLM.lean.agent import EXHAUSTED, NETWORK, SOLVED, LeanAgent, extract_json
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.task import LeanTask
from FormalLLM.llm.provider import LLMProvider

LOOP = {"law": "loop", "state": [["i", "Nat"], ["s", "Nat"]], "init": ["0", "0"],
        "invariant": "s * 2 = i * (i + 1) ∧ i ≤ n", "guard": "i < n", "variant": "n - i", "result": "s"}
BODY = {"law": "term", "expr": "(i + 1, s + (i + 1))"}
WRONG_BODY = {"law": "term", "expr": "(i + 1, s + i)"}


class Script(LLMProvider):
    """Returns the given replies in order; an Exception in the list is raised instead."""

    def __init__(self, replies):
        self.replies, self.prompts = list(replies), []

    def generate(self, prompt, max_tokens=None):
        self.prompts.append(prompt)
        reply = self.replies.pop(0) if self.replies else json.dumps(WRONG_BODY)
        if isinstance(reply, Exception):
            raise reply
        return reply if isinstance(reply, str) else json.dumps(reply, ensure_ascii=False)


@pytest.fixture(scope="module")
def sum_task(tmp_path_factory):
    root = str(tmp_path_factory.mktemp("agent_tasks"))
    directory = write_task(root, "t_sum", "sumTo", [("n", "Nat")], "Nat", "Return 1 + 2 + ... + n.", "True",
                           "2 * result = n * (n + 1)", "(List.range (n + 1)).sum",
                           tests=[{"input": {"n": "4"}, "expected": 10, "unexpected": [11]}])
    return LeanTask.from_dir(directory)


def test_extract_json_finds_the_object_in_prose_and_fences():
    assert extract_json('Sure! ```json\n{"law": "term", "expr": "n"}\n``` done') == {"law": "term", "expr": "n"}
    assert extract_json('{"law": "term", "expr": "f(\\"}\\")"} trailing') == {"law": "term", "expr": 'f("}")'}
    assert extract_json("no object here") is None and extract_json("") is None
    assert extract_json('{"a": 1, "b": {"c": 2}}') == {"a": 1, "b": {"c": 2}}


def test_a_correct_step_by_step_run_is_solved_and_certified(lean_session, sum_task):
    provider = Script([LOOP, BODY])
    result = LeanAgent(provider).solve(sum_task, lean_session)
    assert result.outcome == SOLVED and result.verified
    assert [c.outcome for c in result.calls] == ["applied", "applied"]
    assert "Goal 1: find ρ : Nat" in provider.prompts[0] and "⊢ ∃ ρ, sumTo_postcond n ρ h_precond" in provider.prompts[0]
    assert "Goal 2: find ρ : Nat × Nat" in provider.prompts[1] and "s * 2 = i * (i + 1)" in provider.prompts[1]


def test_a_rejection_is_fed_back_and_the_next_attempt_can_use_it(lean_session, sum_task):
    provider = Script([LOOP, WRONG_BODY, BODY])
    result = LeanAgent(provider).solve(sum_task, lean_session)
    assert result.verified and [c.outcome for c in result.calls] == ["applied", "unproved", "applied"]
    third = provider.prompts[2]
    assert "Earlier attempts on this goal were rejected" in third and "(s + i) * 2" in third
    assert "counter-example" in third


def test_a_nested_reply_is_applied_in_one_call(lean_session, sum_task):
    result = LeanAgent(Script([dict(LOOP, children=[BODY])])).solve(sum_task, lean_session)
    assert result.verified and len(result.calls) == 1


def test_unparsable_replies_use_up_attempts_without_touching_the_derivation(lean_session, sum_task):
    result = LeanAgent(Script(["I think the answer is 42", "no idea"]), attempts_per_goal=2).solve(sum_task, lean_session)
    assert result.outcome == EXHAUSTED and [c.outcome for c in result.calls] == ["unparsable", "unparsable"]
    assert result.derivation.laws_used == 0 and "failed 2 times" in result.detail


def test_a_goal_that_cannot_be_solved_withdraws_the_step_that_created_it(lean_session, sum_task):
    # the body is wrong three times; after that the loop is withdrawn and the parent is asked again
    provider = Script([LOOP, WRONG_BODY, WRONG_BODY, WRONG_BODY, dict(LOOP, children=[BODY])])
    result = LeanAgent(provider, attempts_per_goal=3).solve(sum_task, lean_session)
    assert result.verified and result.retractions == 1
    assert "withdrawn" in provider.prompts[4]


def test_call_budget_is_respected(lean_session, sum_task):
    result = LeanAgent(Script([LOOP, WRONG_BODY, WRONG_BODY, WRONG_BODY]), max_calls=3, attempts_per_goal=9).solve(
        sum_task, lean_session)
    assert result.outcome == EXHAUSTED and len(result.calls) == 3 and "out of model calls" in result.detail


def test_a_dead_endpoint_is_reported_as_network_not_as_a_failure(lean_session, sum_task):
    cut = RuntimeError("HTTP 403: This ngrok account has reached its network bandwidth limit (ERR_NGROK_725)")
    result = LeanAgent(Script([cut])).solve(sum_task, lean_session)
    assert result.outcome == NETWORK and result.calls[0].outcome == "network"


def test_retract_reopens_a_goal_and_forgets_its_descendants(lean_session, sum_task):
    derivation = Derivation(sum_task, lean_session)
    assert all(s.ok for s in derivation.apply_tree(dict(LOOP, children=[BODY])))
    assert derivation.complete and len(derivation.nodes) == 2
    derivation.retract(1)
    assert [g.id for g in derivation.open_goals()] == [1] and len(derivation.nodes) == 1
    assert derivation.laws_used == 0
