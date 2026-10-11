"""The Lean specification library, the lemma library, and the hand-written derivations that tie them to the engine.

Tests that need no Lean check the library's structure and the Python-to-Lean conversions. Tests that run Lean use the shared
session of ``conftest.py`` (skipped when Lean is not installed). The full validation of the library (compile, reference passes
every test, specification accepts the expected outputs and rejects wrong ones) imports all of Mathlib and takes minutes: it is
run by ``python benchmarks/datasets/lean_specs.py validate`` and its stored result is checked here.
"""
import json
import os

import pytest

from benchmarks.datasets import lean_oracle, lean_specs
from benchmarks.datasets.lean_specs import SPECS, expected_json, lean_literal, mutants
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.lemmas import LEMMAS, NAMES
from FormalLLM.lean.task import LeanTask

LIBRARY = lean_specs.LIBRARY
RESULTS = lean_specs.RESULTS


# --- conversions ---------------------------------------------------------------------------------------------------

def test_python_values_become_lean_literals():
    assert lean_literal(-3, "Int") == "-3" and lean_literal(True, "Bool") == "true"
    assert lean_literal("a\"b", "String") == '"a\\"b"' and lean_literal("🧐", "String") == '"🧐"'
    assert lean_literal([[1], [2, 3]], "List (List Int)") == "[[1], [2, 3]]"
    assert lean_literal([1, 2], "List Int") == "[1, 2]" and lean_literal([1, 2], "Array Int") == "#[1, 2]"
    assert lean_literal(None, "Option Int") == "none" and lean_literal(2, "Option Int") == "some (2)"
    assert lean_literal([1, "x"], "Nat × String") == '(1, "x")'
    assert lean_literal(["ab", "c"], "List String") == '["ab", "c"]'


def test_floats_chars_nested_tuples_and_python_bools_have_literals():
    assert lean_literal(0.5, "ℚ") == "(1 / 2 : ℚ)" and lean_literal(3, "ℚ") == "(3 : ℚ)" and lean_literal(-0.25, "ℚ") == "(-1 / 4 : ℚ)"
    assert lean_literal(True, "Int") == "1" and lean_literal(False, "ℚ") == "(0 : ℚ)"          # True + True = 2 in Python
    assert lean_literal("a", "Char") == "'a'" and lean_literal("'", "Char") == "'\\''" and lean_literal("\n", "Char") == "'\\n'"
    assert lean_literal([1, 2, 3], "Int × Int × Int") == "(1, 2, 3)"
    assert lean_literal([("a", 1)], "List (Char × Nat)") == "[('a', 1)]" and lean_literal({"a": 1}, "List (Char × Nat)") == "[('a', 1)]"
    assert lean_literal([[1], []], "List (List Nat)") == "[[1], []]" and lean_literal(None, "Option (List Int)") == "none"
    assert lean_literal([0.5, 2], "List ℚ") == "[(1 / 2 : ℚ), (2 : ℚ)]"


def test_unrepresentable_values_are_refused_not_guessed():
    for value, type_text in ((-1, "Nat"), (1.5, "Int"), ("x", "Int"), (3, "Bool"), ([1], "String"), ("ab", "Char"), (float("nan"), "ℚ")):
        with pytest.raises(ValueError):
            lean_literal(value, type_text)


def test_expected_values_follow_the_test_file_convention():
    assert expected_json(5, "Int") == 5 and expected_json(True, "Bool") == True and expected_json("s", "String") == "s"
    assert expected_json([1, 2], "List Int") == "[1, 2]" and expected_json(None, "Option Int") == "none"


def test_mutants_are_different_wrong_answers():
    for value, type_text in ((True, "Bool"), (5, "Int"), (0, "Nat"), ("abc", "String"), ("", "String"), ([1, 2, 3], "List Int"),
                             ([], "List Int"), (None, "Option Int"), (4, "Option Int"), ([1, "a"], "Nat × String")):
        wrong = mutants(value, type_text)
        assert wrong, (value, type_text)
        assert all(m != value for m in wrong) and len({json.dumps(m) for m in wrong}) == len(wrong)
    assert all(m >= 0 for m in mutants(0, "Nat"))


# --- the library on disk -------------------------------------------------------------------------------------------

def test_library_has_at_least_forty_distinct_specifications():
    assert len(SPECS) >= 40 and len({s.id for s in SPECS}) == len(SPECS) and len({s.name for s in SPECS}) == len(SPECS)
    humaneval = [s.source for s in SPECS if s.source.startswith("HumanEval")]
    assert len(set(humaneval)) == len(humaneval) >= 37                    # one HumanEval problem each
    assert {s.id for s in SPECS if s.source == "original"} >= {"classic_isqrt", "classic_sqrt_approx", "classic_sort_list"}


@pytest.mark.parametrize("spec", SPECS, ids=lambda s: s.id)
def test_each_task_directory_is_complete_and_loads(spec):
    directory = os.path.join(LIBRARY, spec.id)
    if not os.path.isdir(directory):
        pytest.skip("library not built: python benchmarks/datasets/lean_specs.py build")
    for name in ("task.json", "description.txt", "task.lean", "test.json"):
        assert os.path.exists(os.path.join(directory, name)), name
    task = LeanTask.from_dir(directory)
    assert task.name == spec.name and task.params == spec.params and task.ret == spec.ret
    assert len(task.tests) >= 3
    for case in task.tests:
        assert set(case["input"]) == {n for n, _ in spec.params} and "expected" in case
    assert f"def {spec.name}_precond" in task.prelude and f"def {spec.name}_postcond" in task.prelude
    assert f"def {spec.name} " not in task.prelude                        # the reference solution is not in what the engine sees
    assert "sorry" not in task.prelude


def test_stored_validation_covers_every_specification_and_found_no_problem():
    path = os.path.join(RESULTS, "validation.json")
    if not os.path.exists(path):
        pytest.skip("run: python benchmarks/datasets/lean_specs.py validate")
    rows = {r["id"]: r for r in json.load(open(path, encoding="utf8"))}
    assert set(rows) == {s.id for s in SPECS}
    for row in rows.values():
        assert row["compiles"] and row["reference_passes"] == row["tests"] == row["accepts_expected"], row["id"]
        assert row["wrong_total"] > 0 and row["undecidable"] == 0, row["id"]
        # a specification that accepts several right answers (a dictionary has no order) may accept a "wrong" output that is
        # the same dictionary reordered; every other specification must reject all of them
        assert row["rejects_wrong"] == row["wrong_total"] or row["permissive"], row["id"]


# --- the lemma library ---------------------------------------------------------------------------------------------

def test_lemmas_are_proved_without_sorry(lean_session):
    check = LEMMAS + "\n" + "\n".join(f"#print axioms Refine.{name}" for name in NAMES)
    reply = lean_session.run(check)
    assert reply.errors == [] and reply.goals == []
    assert len(reply.infos) == len(NAMES)
    assert not any("sorryAx" in info for info in reply.infos)


# --- the hand-written derivations ----------------------------------------------------------------------------------

def test_every_oracle_belongs_to_a_specification():
    assert set(lean_oracle.ORACLES) <= {s.id for s in SPECS}
    assert len(lean_oracle.ORACLES) >= 30


@pytest.mark.parametrize("task_id", ["he_060_sum_to_n", "he_100_make_a_pile", "he_057_monotonic", "he_150_x_or_y",
                                     "he_098_count_upper", "he_126_is_sorted", "he_003_below_zero", "he_030_get_positive",
                                     "classic_isqrt", "classic_fast_power", "classic_reverse", "classic_sort_list"])
def test_oracle_derivations_are_certified(lean_session, task_id):
    directory = os.path.join(LIBRARY, task_id)
    if not os.path.isdir(directory):
        pytest.skip("library not built")
    derivation = Derivation(LeanTask.from_dir(directory), lean_session)
    steps = derivation.apply_tree(lean_oracle.ORACLES[task_id])
    assert all(s.ok for s in steps), steps[-1].feedback()
    certificate = derivation.certify()
    assert certificate.verified, certificate
    assert certificate.passed == certificate.tests > 0
