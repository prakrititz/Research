"""The HumanEval pilot pipeline, end to end, with a scripted model (no network)."""
import json
import os
import sys
from types import SimpleNamespace

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

he = pytest.importorskip("benchmarks.datasets.humaneval")
pytestmark = pytest.mark.skipif(not he.EVALPLUS_AVAILABLE, reason="evalplus is not installed")

from benchmarks import run_bench                                    # noqa: E402
from benchmarks.datasets import he_refine, he_specs                 # noqa: E402
from FormalLLM.llm.provider import MockProvider                     # noqa: E402


def reply(**body):
    return json.dumps(body)


def args(out, tasks, **extra):
    base = dict(config="gpt-oss-120b-low", tasks=tasks, repeats=1, turns=2, budget=10, max_retries=3,
                max_depth=6, temperature=0.2, timeout=60, assist=False, strict="0", backend="z3",
                certify=None, out=str(out), baseline=None)
    base.update(extra)
    return SimpleNamespace(**base)


def run_scripted(monkeypatch, tmp_path, task, replies, **extra):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    provider = MockProvider(replies)
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: provider)
    out = tmp_path / "rows.jsonl"
    he_refine.run(args(out, [task], **extra))
    return [json.loads(line) for line in out.read_text(encoding="utf8").splitlines()]


def test_a_derived_assignment_passes_every_test(monkeypatch, tmp_path):
    rows = run_scripted(monkeypatch, tmp_path, "HumanEval/41",
                        [reply(law="assignment"), reply(parameters={"variable": "r", "expr": "n * n"})])
    assert rows[0]["outcome"] == "SUCCESS" and rows[0]["llm_calls"] == 2
    assert rows[0]["base"] == "pass" and rows[0]["plus"] == "pass"
    assert "return r" in he_refine.build_solution("HumanEval/41", rows[0]["python"])


def test_whole_number_division_survives_into_the_tests(monkeypatch, tmp_path):
    """`n = 2 * (n / 2)` is an evenness test only with whole-number division; HumanEval/138 would
    fail its tests if the emitted Python used true division."""
    rows = run_scripted(monkeypatch, tmp_path, "HumanEval/138",
                        [reply(law="assignment"),
                         reply(parameters={"variable": "t", "expr": "n >= 8 && n = 2 * (n / 2)"})])
    assert rows[0]["outcome"] == "SUCCESS" and "//" in rows[0]["python"]
    assert rows[0]["base"] == "pass" and rows[0]["plus"] == "pass"


def test_a_wrong_but_proved_program_is_caught_by_the_tests_not_hidden(monkeypatch, tmp_path):
    """A specification that is weaker than the problem would let a wrong program through the prover;
    the real tests are the second line of defence. Here the prover rejects, so nothing is derived."""
    rows = run_scripted(monkeypatch, tmp_path, "HumanEval/41",
                        [reply(law="assignment")] + [reply(parameters={"variable": "r", "expr": "n + n"})] * 3,
                        max_retries=2)
    assert rows[0]["outcome"] in ("EXHAUSTED", "BUDGET") and rows[0]["base"] is None


def test_the_solution_wrapper_binds_lengths_and_returns_the_result():
    source = he_refine.build_solution("HumanEval/52", "b = True\ni = 0")
    assert "def below_threshold(l, t):" in source and "n = len(l)" in source and source.rstrip().endswith("return b")


def test_every_pilot_specification_has_a_complete_table_entry():
    for task_id, entry in he_specs.SPECS.items():
        assert {"name", "spec", "args", "bind", "result", "tier"} <= set(entry), task_id
        assert he_refine.function_parameters(task_id) == entry["args"] or \
            len(he_refine.function_parameters(task_id)) == len(entry["args"])


def test_a_stored_pilot_row_replays_to_the_same_program(monkeypatch, tmp_path):
    """The reproducibility claim: the stored replies alone re-derive the same program, offline."""
    from benchmarks import replay
    rows = run_scripted(monkeypatch, tmp_path, "HumanEval/138",
                        [reply(law="assignment"),
                         reply(parameters={"variable": "t", "expr": "n >= 8 && n = 2 * (n / 2)"})])
    options = SimpleNamespace(turns=2, max_retries=3, max_depth=6, assist=False, certify=None)
    outcome, calls, program, _ = replay.replay_row(rows[0], {}, options)
    assert (outcome, calls) == ("SUCCESS", 2)
    assert program == rows[0]["program"] and "t = " in program


class Unreachable:
    """A provider whose every call fails the way the real one does when the network is down."""
    def __init__(self, *a, **k):
        self.calls = 0

    def generate(self, *a, **k):
        from FormalLLM.llm.provider import LLMProvider  # noqa: F401  (import check only)
        raise ConnectionError("Failed to reach https://example.invalid after 3 attempts: getaddrinfo failed")


def test_a_run_that_never_reached_the_model_is_labelled_network_not_failed(monkeypatch, tmp_path, capsys):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: Unreachable())
    out = tmp_path / "rows.jsonl"
    he_refine.run(args(out, ["HumanEval/41"]))
    rows = [json.loads(line) for line in out.read_text(encoding="utf8").splitlines()]
    assert rows[0]["outcome"] == "NETWORK" and rows[0]["graph"]["error_messages"]
    he_refine.summarize(str(out))
    printed = capsys.readouterr().out
    assert "0 of 0 runs derived" in printed and "never reached the model" in printed


def test_a_network_row_is_run_again_when_the_same_command_is_repeated(monkeypatch, tmp_path):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    out = tmp_path / "rows.jsonl"
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: Unreachable())
    he_refine.run(args(out, ["HumanEval/41"]))
    provider = MockProvider([reply(law="assignment"), reply(parameters={"variable": "r", "expr": "n * n"})])
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: provider)
    he_refine.run(args(out, ["HumanEval/41"]))
    rows = [json.loads(line) for line in out.read_text(encoding="utf8").splitlines()]
    assert [r["outcome"] for r in rows] == ["NETWORK", "SUCCESS"]
    assert rows[1]["base"] == "pass" and rows[1]["plus"] == "pass"
    he_refine.run(args(out, ["HumanEval/41"]))                                  # a finished run is not repeated
    assert len(out.read_text(encoding="utf8").splitlines()) == 2


def test_the_preflight_stops_the_command_line_run_before_anything_starts(monkeypatch, tmp_path):
    from benchmarks import reliability_batch
    monkeypatch.setattr(reliability_batch, "preflight", lambda a: (False, "ConnectionError: down"))
    monkeypatch.setattr(sys, "argv", ["he_refine", "--out", str(tmp_path / "x.jsonl")])
    with pytest.raises(SystemExit) as stopped:
        he_refine.main()
    assert "could not be reached" in str(stopped.value)
    assert not (tmp_path / "x.jsonl").exists()
