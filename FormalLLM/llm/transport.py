"""Telling a trial that was *lost* from a trial that *failed*.

A refinement trial can end without a result for two very different reasons. Either the search ran
out of options or calls (the method failed on this problem), or the model never answered because
the network was down (nothing was learned about the method). Counting the second kind as a
failure lowers a success rate for a reason that has nothing to do with refinement; it happened in
the v6 square-root study, where one trial of 100 died on ``getaddrinfo failed`` and was filed
under EXHAUSTED.

A trial is *lost to the network* only when every model call failed to connect: each call returned
nothing and each recorded error is the provider's "Failed to reach <url> after N attempts"
(``OpenAIChatProvider.generate``). One real reply anywhere makes the trial a genuine one.

A trial is also *cut off* when the endpoint stopped serving altogether in the middle of it. On the
morning of 2026-10-05 the tunnel to the hosted model reached its monthly bandwidth limit and answered
every call with ``HTTP 403: This ngrok account has reached its network bandwidth limit``; trials
running then ended after a few calls and were filed as EXHAUSTED, as if the method had failed. Such an
error means the model was never consulted for that call and could not be consulted again, so a trial
that recorded one did not get its call budget and says nothing about the method either way.
"""
from typing import Any, Dict, Iterable

#: The start of the provider's message when all its transport retries are used up
#: (FormalLLM/llm/provider.py; tests/test_network_outcome.py checks it is still there).
TRANSPORT_FAILURE_MARK = "Failed to reach"

#: Errors that mean the endpoint itself stopped serving (not a reply the model gave).
ENDPOINT_CUTOFF_MARKS = ("network bandwidth limit", "ERR_NGROK")

#: The outcome label for such a trial.
NETWORK = "NETWORK"


def cut_off_by_endpoint(error_messages: Iterable[str]) -> bool:
    """True when some call failed because the endpoint stopped serving (e.g. the tunnel's bandwidth limit)."""
    return any(mark in str(e) for e in error_messages for mark in ENDPOINT_CUTOFF_MARKS)


def lost_to_network(responses: Iterable[Any], error_messages: Iterable[str]) -> bool:
    """True when the model was never consulted: every call returned nothing and every error is a transport failure."""
    responses, errors = list(responses), list(error_messages)
    if not responses or not errors:
        return False
    if any(str(r or "").strip() for r in responses):
        return False
    return all(TRANSPORT_FAILURE_MARK in str(e) for e in errors)


def effective_outcome(record: Dict[str, Any]) -> str:
    """A stored trial's outcome, with the network-lost ones recognised (also in files written before this existed)."""
    outcome = record.get("outcome")
    errors = (record.get("graph") or {}).get("error_messages") or []
    if outcome != "SUCCESS" and (lost_to_network(record.get("raw_responses") or [], errors)
                                 or cut_off_by_endpoint(errors) or cut_off_by_endpoint([record.get("detail") or ""])):
        return NETWORK
    return outcome
