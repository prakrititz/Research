"""A Z3 run that times out is repeated from scratch under another seed before an obligation is called unknown.

Z3's running time on one obligation is wildly uneven (the same text: a few milliseconds on one run, the
whole 10 s limit on the next), so a few short runs followed by one patient run proves far more than a
single patient run. A proof is a proof whatever the seed, so this can only turn "unknown" into an answer.
"""
import z3

from FormalLLM.lspec.parser import parse_spec
from FormalLLM.verification import z3_backend as zb
from FormalLLM.verification.proof_obligations import ProofObligation

TIMEOUT = "timeout"
UNKNOWN = (z3.unknown, TIMEOUT)
PROVED = (z3.unsat, "")


def obligation(pre, post):
    spec = parse_spec(f"Precondition: (x:int) := {pre}.\nPostcondition: (x:int) := {post}.")
    return ProofObligation([spec.precondition.expr], spec.postcondition.expr, params=spec.precondition.params)


class FakeSolver:
    def __init__(self, reason):
        self.reason = reason

    def reason_unknown(self):
        return self.reason


class Scripted:
    """Stands for one Z3 run per call: answers from a script and records the limit and seed it was given."""

    def __init__(self, *answers):
        self.answers = list(answers)
        self.calls = []

    def __call__(self, obl, timeout_ms, seed=None):
        self.calls.append((timeout_ms, seed))
        result, reason = self.answers.pop(0)
        return FakeSolver(reason), object(), result


def run(monkeypatch, scripted, timeout_ms=None):
    monkeypatch.setattr(zb, "_attempt", scripted)
    return zb.verify_obligation(obligation("x > 0", "x >= 0"), timeout_ms=timeout_ms)


def test_the_runs_are_a_few_short_ones_and_then_one_with_the_whole_budget():
    assert zb._plan(10_000, 4) == [(1000, None), (1000, 1), (1000, 2), (1000, 3), (10_000, 4)]
    assert zb._plan(1_000, 3) == [(300, None), (300, 1), (300, 2), (1_000, 3)]
    assert zb._plan(10_000, 0) == [(10_000, None)]


def test_a_timeout_is_followed_by_a_fresh_run_and_a_later_proof_counts(monkeypatch):
    scripted = Scripted(UNKNOWN, UNKNOWN, PROVED)
    before = dict(zb.RETRY_STATS)
    status, _ = run(monkeypatch, scripted)
    assert status == "PROVED"
    assert scripted.calls == [(1000, None), (1000, 1), (1000, 2)]
    assert zb.RETRY_STATS["rescued"] == before["rescued"] + 1


def test_a_proof_on_the_first_run_makes_no_other_run(monkeypatch):
    scripted = Scripted(PROVED)
    assert run(monkeypatch, scripted)[0] == "PROVED"
    assert scripted.calls == [(1000, None)]


def test_when_every_run_times_out_the_answer_is_unknown_and_the_whole_budget_was_tried_once(monkeypatch):
    scripted = Scripted(UNKNOWN, UNKNOWN, UNKNOWN, UNKNOWN, UNKNOWN)
    before = zb.RETRY_STATS["gave_up"]
    status, message = run(monkeypatch, scripted)
    assert status == "UNKNOWN" and "timeout" in message
    assert scripted.calls[-1] == (10_000, 4) and len(scripted.calls) == 5
    assert zb.RETRY_STATS["gave_up"] == before + 1


def test_a_budget_given_by_the_caller_means_a_single_run(monkeypatch):
    scripted = Scripted(UNKNOWN)
    assert run(monkeypatch, scripted, timeout_ms=1500)[0] == "UNKNOWN"
    assert scripted.calls == [(1500, None)]


def test_an_unknown_that_is_not_a_timeout_is_not_retried(monkeypatch):
    scripted = Scripted((z3.unknown, "incomplete quantifiers"))
    assert run(monkeypatch, scripted)[0] == "UNKNOWN"
    assert len(scripted.calls) == 1


def test_retries_can_be_switched_off(monkeypatch):
    monkeypatch.setenv("FORMALLLM_Z3_RETRIES", "0")
    scripted = Scripted(UNKNOWN)
    assert run(monkeypatch, scripted)[0] == "UNKNOWN"
    assert scripted.calls == [(10_000, None)]


def test_a_z3_without_the_seed_parameters_still_gets_its_fresh_run(monkeypatch):
    calls = []

    def attempt(obl, timeout_ms, seed=None):
        calls.append((timeout_ms, seed))
        if seed is not None:
            raise z3.Z3Exception("unknown parameter 'random_seed'")
        return FakeSolver(TIMEOUT if len(calls) == 1 else ""), object(), z3.unknown if len(calls) == 1 else z3.unsat

    monkeypatch.setattr(zb, "_attempt", attempt)
    status, _ = zb.verify_obligation(obligation("x > 0", "x >= 0"))
    assert status == "PROVED"
    assert calls == [(1000, None), (1000, 1), (1000, None)]


def test_the_seed_changes_the_run_not_the_answer():
    valid, invalid = obligation("x > 0", "x >= 0"), obligation("x >= 0", "x > 0")
    for seed in range(6):
        assert zb._attempt(valid, 2000, seed)[2] == z3.unsat
        assert zb._attempt(invalid, 2000, seed)[2] == z3.sat


def test_a_counterexample_found_by_a_later_run_is_still_reported(monkeypatch):
    real = zb._attempt
    calls = []

    def attempt(obl, timeout_ms, seed=None):
        calls.append(seed)
        if len(calls) == 1:
            return FakeSolver(TIMEOUT), object(), z3.unknown
        return real(obl, timeout_ms, seed)

    monkeypatch.setattr(zb, "_attempt", attempt)
    status, message = zb.verify_obligation(obligation("x >= 0", "x > 0"))
    assert status == "FAILED" and "x = 0" in message and calls == [None, 1]
