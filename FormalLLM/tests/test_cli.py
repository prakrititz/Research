"""The command line: one command from specification to a checked program."""
import json
import os
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

import main as cli                                    # noqa: E402
from benchmarks import run_bench                      # noqa: E402
from FormalLLM.llm.provider import MockProvider       # noqa: E402

WEAK = {"invariant": "x * x <= N", "guard": "N >= (x + e) * (x + e)", "variant": "N - (x + e) * (x + e)"}
STRONG = {"invariant": "x * x <= N && x >= 0", "guard": "N >= (x + e) * (x + e)",
          "variant": "N - (x + e) * (x + e)"}


def reply(law, **parameters):
    return json.dumps({"law": law, "parameters": parameters})


def script():
    # two-turn mode: law, then parameters (the repair costs one more parameter call)
    return [reply("initialised_iteration"), reply("initialised_iteration", **WEAK),
            reply("initialised_iteration", **STRONG)]


@pytest.fixture
def scripted(monkeypatch):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    provider = MockProvider(script())
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: provider)
    return provider


def test_the_paper_example_runs_end_to_end(scripted, capsys):
    status = cli.main(["--assist", "--run", "N=10,e=1", "--quiet"])
    out = capsys.readouterr().out
    assert status == 0
    assert "SUCCESS: 3 LLM call(s)" in out and "closed by the prover alone" in out
    assert "x = 0\nwhile (N >= ((x + e) * (x + e))):\n  x = (x + e)" in out
    assert "{'x': 3}" in out, "x = 3 is the integer square root of 10 for e = 1"
    assert "Its simplest candidate, x := x + e, is refuted" in out, "the repaired step stays in the trace"


def test_the_summary_is_written_without_secrets(scripted, tmp_path, monkeypatch):
    monkeypatch.setenv("FORMALLLM_REMOTE_AUTH", "someone:not-a-real-password")
    target = tmp_path / "result.json"
    assert cli.main(["--assist", "--quiet", "--json", str(target)]) == 0
    text = target.read_text(encoding="utf8")
    assert json.loads(text)["outcome"] == "SUCCESS"
    assert "not-a-real-password" not in text and "someone" not in text


def test_without_the_assist_the_leaves_go_to_the_model(monkeypatch, capsys):
    monkeypatch.setenv("FORMALLLM_STRICT_VARIANT", "0")
    provider = MockProvider([reply("initialised_iteration"), reply("initialised_iteration", **STRONG)])
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: provider)
    status = cli.main(["--quiet", "--budget", "2"])
    out = capsys.readouterr().out
    assert status == 1 and "BUDGET" in out


def test_cases_can_be_listed(capsys):
    assert cli.main(["--list-cases"]) == 0
    assert "C5-sqrt-paper" in capsys.readouterr().out


def test_inputs_are_parsed():
    assert cli.parse_inputs("N=10,e=0.5") == {"N": 10, "e": 0.5}
