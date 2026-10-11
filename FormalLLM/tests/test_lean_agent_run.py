"""The runner around the Lean agent: per-problem scoring, trial records, replay without a model."""
import json
import os

import pytest

from benchmarks import lean_agent_run as runner
from benchmarks.datasets.lean_oracle import ORACLES
from FormalLLM.lean.agent import LeanAgent
from FormalLLM.lean.task import LeanTask
from FormalLLM.llm.provider import LLMProvider

TASK = "he_060_sum_to_n"
needs_library = pytest.mark.skipif(not os.path.isdir(os.path.join(runner.LIBRARIES["lean_specs"], TASK)),
                                   reason="library not built: python benchmarks/datasets/lean_specs.py build")


class Script(LLMProvider):
    def __init__(self, replies):
        self.replies = list(replies)

    def generate(self, prompt, max_tokens=None):
        return self.replies.pop(0) if self.replies else ""


def trial(task, number, outcome, verified):
    return {"task": task, "trial": number, "outcome": outcome, "verified": verified}


def test_per_problem_scoring_leaves_network_trials_out_of_the_fraction():
    rows = [trial("a", 0, "SOLVED", True), trial("a", 1, "SOLVED", True), trial("a", 2, "NETWORK", False),
            trial("b", 0, "SOLVED", True), trial("b", 1, "EXHAUSTED", False), trial("c", 0, "EXHAUSTED", False)]
    table = runner.solved_table(rows)
    assert table == {"a": (2, 2, 1), "b": (2, 1, 0), "c": (1, 0, 0)}


def test_summary_reports_thresholds_and_the_mean(tmp_path, capsys):
    path = tmp_path / "t.jsonl"
    rows = [trial("a", 0, "SOLVED", True), trial("a", 1, "SOLVED", True), trial("b", 0, "SOLVED", True),
            trial("b", 1, "EXHAUSTED", False), trial("c", 0, "EXHAUSTED", False)]
    path.write_text("\n".join(json.dumps(r) for r in rows), encoding="utf8")
    text = runner.summarize(str(path))
    assert ">= 100%: 1/3" in text and ">= 50%: 2/3" in text and ">= 20%: 2/3" in text
    assert "Mean per-problem verified rate: 0.500" in text


@needs_library
def test_a_trial_is_recorded_with_its_replies_and_replays_to_the_same_outcome(lean_session, tmp_path):
    task = LeanTask.from_dir(os.path.join(runner.LIBRARIES["lean_specs"], TASK))
    replies = ["not json at all", json.dumps(ORACLES[TASK], ensure_ascii=False)]
    result = LeanAgent(Script(replies)).solve(task, lean_session)
    assert result.verified
    row = runner.record(TASK, 0, result, 1.5, "scripted")
    assert row["calls"] == 2 and row["call_outcomes"] == ["unparsable", "applied"] and row["replies"] == replies
    assert row["certificate"]["passed"] == row["certificate"]["tests"] > 0 and row["tree"]["law"] == "loop"
    path = tmp_path / "trials.jsonl"
    path.write_text(json.dumps(row, ensure_ascii=False) + "\n", encoding="utf8")
    assert runner.replay(str(path)) == 0                                       # reproduced: no mismatch


@needs_library
def test_replay_notices_a_stored_outcome_that_is_no_longer_reproduced(lean_session, tmp_path):
    task = LeanTask.from_dir(os.path.join(runner.LIBRARIES["lean_specs"], TASK))
    result = LeanAgent(Script([json.dumps(ORACLES[TASK])])).solve(task, lean_session)
    row = runner.record(TASK, 0, result, 1.0, "scripted")
    row["replies"] = ["{}"]                                                    # tampered: the stored replies no longer solve it
    path = tmp_path / "trials.jsonl"
    path.write_text(json.dumps(row, ensure_ascii=False) + "\n", encoding="utf8")
    assert runner.replay(str(path)) == 1
