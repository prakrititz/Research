"""A trial that never reached the model is NETWORK, not a refinement failure (no network needed)."""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

from FormalLLM.llm.provider import LLMProvider, MockProvider                         # noqa: E402
from FormalLLM.llm.transport import TRANSPORT_FAILURE_MARK, effective_outcome, lost_to_network  # noqa: E402
import summarize_reliability as sr                                                  # noqa: E402

DOWN = ("Exception: Failed to reach https://example.invalid/v1 after 4 attempts. "
        "Error: <urlopen error [Errno 11001] getaddrinfo failed>")


def record(outcome="EXHAUSTED", responses=("", "", "", ""), errors=(DOWN,) * 4, calls=4):
    return {"outcome": outcome, "llm_calls": calls, "wall_s": 5.0, "raw_responses": list(responses),
            "graph": {"error_messages": list(errors)}}


def test_every_call_failing_to_connect_is_a_lost_trial():
    assert lost_to_network(["", "  ", None], [DOWN, DOWN, DOWN])
    assert effective_outcome(record()) == "NETWORK"


def test_one_real_reply_makes_it_a_genuine_trial():
    assert not lost_to_network(["", "{\"law\": \"skip\"}"], [DOWN])
    assert effective_outcome(record(responses=("", "{}"))) == "EXHAUSTED"


def test_any_other_error_keeps_it_a_genuine_failure():
    assert not lost_to_network(["", ""], [DOWN, "ValueError: could not parse the reply"])
    assert effective_outcome(record(errors=(DOWN, DOWN, DOWN, "KeyError: 'law'"))) == "EXHAUSTED"


def test_no_calls_or_no_errors_is_not_called_lost():
    assert not lost_to_network([], [DOWN])
    assert not lost_to_network([""], [])


def test_success_is_never_relabelled():
    assert effective_outcome(record(outcome="SUCCESS")) == "SUCCESS"


def test_the_marker_is_still_the_providers_message():
    source = open(os.path.join(ROOT, "FormalLLM", "llm", "provider.py"), encoding="utf8").read()
    assert TRANSPORT_FAILURE_MARK in source


def test_summary_leaves_lost_trials_out_of_the_rate_but_shows_them():
    rows = [record("SUCCESS", responses=("{}",), errors=()) for _ in range(9)] + [record()]
    s = sr.summarize(rows)
    assert (s["ok"], s["n"], s["n_all"]) == (9, 9, 10)
    assert s["outcomes"] == {"SUCCESS": 9, "NETWORK": 1}
    assert s["low"] > 0.66                                          # 9/9 is judged on 9 trials, not 9/10


class Unreachable(LLMProvider):
    def generate(self, prompt, max_tokens=None):
        raise Exception("Failed to reach https://example.invalid/v1 after 4 attempts. Error: boom")


def test_a_real_trial_against_an_unreachable_model_is_labelled_network():
    from cases import CASES_BY_ID
    from harness import run_trial
    rec = run_trial(CASES_BY_ID["A2-assign"], Unreachable(), 0, "none", budget=10)
    assert rec["outcome"] == "NETWORK" and "unreachable" in rec["detail"]
    json.dumps(rec)                                                  # still a storable record


def test_a_model_that_answers_nonsense_is_still_a_real_failure():
    from cases import CASES_BY_ID
    from harness import run_trial
    rec = run_trial(CASES_BY_ID["A2-assign"], MockProvider(["nonsense"] * 40), 0, "mock", budget=10)
    assert rec["outcome"] in ("EXHAUSTED", "BUDGET", "FAILED")


def test_a_trial_cut_off_by_the_endpoint_bandwidth_limit_is_not_a_method_failure():
    """2026-10-05: the tunnel answered every call with HTTP 403 (monthly bandwidth limit); trials then ended after
    a few calls as EXHAUSTED. A trial that recorded such an error did not get its call budget."""
    from FormalLLM.llm.transport import NETWORK, effective_outcome
    cut = ("Exception: https://example.ngrok-free.dev/v1 returned HTTP 403: This ngrok account has reached its "
           "network bandwidth limit for the month.")
    partly = {"outcome": "EXHAUSTED", "raw_responses": ['{"law": "skip"}', ""],
              "graph": {"error_messages": ["Refinement invalid.", cut]}}
    assert effective_outcome(partly) == NETWORK
    genuine = {"outcome": "BUDGET", "raw_responses": ['{"law": "skip"}'], "graph": {"error_messages": ["Refinement invalid."]}}
    assert effective_outcome(genuine) == "BUDGET"
    assert effective_outcome({"outcome": "SUCCESS", "graph": {"error_messages": [cut]}}) == "SUCCESS"
