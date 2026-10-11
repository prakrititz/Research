"""The multi-case reliability driver: planning, resuming, and the summary step (no model, no network)."""
import json
import os
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

import reliability_batch as rb                                        # noqa: E402


@pytest.fixture()
def results(tmp_path, monkeypatch):
    monkeypatch.setattr(rb, "RESULTS", str(tmp_path))
    return tmp_path


def write_trials(folder, label, records, stamp="20261004-120000"):
    path = folder / f"{label}_{stamp}.jsonl"
    path.write_text("".join(json.dumps(r) + "\n" for r in records), encoding="utf8")
    return path


def record(case_id, outcome="SUCCESS", program="x = 0\n"):
    return {"case_id": case_id, "outcome": outcome, "llm_calls": 2, "wall_s": 10.0, "program_python": program}


def test_default_plan_skips_the_square_root_and_treats_a4_as_a_control(results):
    steps = rb.plan(rb.parse_args([]))
    ids = [s["case"] for s in steps]
    assert "C5-sqrt-paper" not in ids and len(ids) == 12
    a4 = next(s for s in steps if s["case"] == "A4-impossible")
    assert a4["control"] and a4["todo"] == 5
    assert ids[-1] == "A4-impossible"                                   # the slow control runs last
    assert all(s["todo"] == 20 for s in steps if not s["control"])


def test_a_rerun_only_runs_the_missing_trials(results):
    write_trials(results, "cases_B2-max", [record("B2-max")] * 7)
    write_trials(results, "cases_B2-max", [record("B2-max")] * 3, stamp="20261004-130000")
    write_trials(results, "cases_A1-skip", [record("A1-skip")] * 20)
    steps = {s["case"]: s for s in rb.plan(rb.parse_args([]))}
    assert steps["B2-max"]["have"] == 10 and steps["B2-max"]["todo"] == 10
    assert steps["A1-skip"]["todo"] == 0                              # finished: not run again
    assert "--trials 10" in " ".join(steps["B2-max"]["cmd"])


def test_the_command_uses_the_studies_protocol_and_a_per_case_label():
    args = rb.parse_args(["--cases", "C4-loop-invariant", "--prefix", "p"])
    cmd = rb.build_command(args, "C4-loop-invariant", 8)
    text = " ".join(cmd)
    for part in ("--case C4-loop-invariant", "--trials 8", "--strict 0", "--turns 2", "--budget 30",
                 "--label p_C4-loop-invariant", "--assist", "--certify coq"):
        assert part in text


def test_switches_for_the_assist_and_for_certification():
    args = rb.parse_args(["--no-assist", "--certify"])
    cmd = rb.build_command(args, "B2-max", 3)
    assert "--assist" not in cmd and "--certify" not in cmd
    both = rb.build_command(rb.parse_args(["--certify", "coq", "lean"]), "B2-max", 3)
    assert both[both.index("--certify"):][:3] == ["--certify", "coq", "lean"]


def test_an_unknown_case_is_refused_clearly():
    with pytest.raises(SystemExit, match="unknown case"):
        rb.plan(rb.parse_args(["--cases", "Z9-nope"]), counts={})


def test_dry_run_needs_no_credentials_and_calls_nothing(results, monkeypatch, capsys):
    monkeypatch.delenv("FORMALLLM_REMOTE_AUTH", raising=False)
    assert rb.main(["--dry-run", "--cases", "B2-max"]) == 0
    out = capsys.readouterr().out
    assert "B2-max" in out and "reliability.py" in out


def test_summary_and_cross_check_are_written_and_an_impossible_success_raises_the_alarm(results, capsys):
    good = "x = 0\nwhile (N >= ((x + e) * (x + e))):\n    x = (x + e)\n"
    write_trials(results, "t_C5-sqrt-paper", [record("C5-sqrt-paper", program=good)] * 3)
    write_trials(results, "t_A4-impossible", [record("A4-impossible", program="y = A\n")])
    args = rb.parse_args(["--prefix", "t", "--cases", "C5-sqrt-paper", "A4-impossible"])
    rb.finish(args, rb.plan(args))
    out = capsys.readouterr().out
    assert "SOUNDNESS ALERT" in out and "A4-impossible" in out
    assert (results / "t_summary.md").read_text(encoding="utf8").count("|") > 10
    cross = (results / "t_cross_check.txt").read_text(encoding="utf8")
    assert "C5-sqrt-paper" in cross and "3" in cross                   # three derivations, one program


# ---------------------------------------------------------------- the model check before each case
class FakeModel:
    def __init__(self, fail=False):
        self.fail = fail

    def generate(self, prompt, max_tokens=None):
        if self.fail:
            raise Exception("Failed to reach https://example.invalid/v1 after 4 attempts. Error: getaddrinfo failed")
        return '{"ok": true}'


def test_preflight_tells_a_reachable_model_from_an_unreachable_one(monkeypatch):
    import run_bench
    args = rb.parse_args([])
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: FakeModel())
    assert rb.preflight(args)[0] is True
    monkeypatch.setattr(run_bench, "make_provider", lambda *a, **k: FakeModel(fail=True))
    ok, note = rb.preflight(args)
    assert ok is False and "Failed to reach" in note


def test_an_unreachable_model_stops_the_batch_before_any_trial(results, monkeypatch, capsys):
    monkeypatch.setenv("FORMALLLM_REMOTE_AUTH", "someone:not-a-real-password")
    monkeypatch.setattr(rb, "preflight", lambda args: (False, "Exception: boom"))

    def must_not_run(*a, **k):
        raise AssertionError("a trial was started although the model is unreachable")
    monkeypatch.setattr(rb.subprocess, "run", must_not_run)
    assert rb.main(["--cases", "B2-max"]) == 1
    assert "could not be reached" in capsys.readouterr().out


def test_the_batch_stops_when_the_model_goes_away_between_cases(results, monkeypatch, capsys):
    from types import SimpleNamespace
    monkeypatch.setenv("FORMALLLM_REMOTE_AUTH", "someone:not-a-real-password")
    answers = iter([(True, "ok"), (False, "Exception: gone")])
    monkeypatch.setattr(rb, "preflight", lambda args: next(answers))
    started = []
    monkeypatch.setattr(rb.subprocess, "run", lambda cmd, **k: started.append(cmd) or SimpleNamespace(returncode=0))
    assert rb.main(["--cases", "A1-skip", "A2-assign", "B2-max"]) == 1
    assert len(started) == 1 and "A1-skip" in " ".join(started[0])           # the first case ran, then it stopped


def test_no_preflight_switch_skips_the_check(results, monkeypatch):
    from types import SimpleNamespace
    monkeypatch.setenv("FORMALLLM_REMOTE_AUTH", "someone:not-a-real-password")
    monkeypatch.setattr(rb, "preflight", lambda args: (_ for _ in ()).throw(AssertionError("should not be called")))
    monkeypatch.setattr(rb.subprocess, "run", lambda cmd, **k: SimpleNamespace(returncode=0))
    assert rb.main(["--cases", "A1-skip", "--no-preflight"]) == 0
