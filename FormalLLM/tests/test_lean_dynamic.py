"""Counter-examples found by running the loop (FormalLLM/lean/dynamic.py)."""
import copy
import os

import pytest

from benchmarks.datasets.lean_oracle import LIBRARY, ORACLES
from FormalLLM.lean import dynamic
from FormalLLM.lean.engine import Derivation
from FormalLLM.lean.task import LeanTask


def test_inputs_printed_by_plausible_are_read_back_in_parameter_order():
    text = "l := [3, -1], t := 5"
    assert dynamic.parse_inputs(text, ["l", "t"]) == ["[3, -1]", "5"]
    assert dynamic.parse_inputs("a := #[1, 2]", ["a"]) == ["#[1, 2]"]
    assert dynamic.parse_inputs("s := \"x := 1\"", ["s"]) == ['"x := 1"']
    assert dynamic.parse_inputs("l := []", ["l", "t"]) is None                      # a value is missing: no trace is built


def test_nested_projections_follow_the_shape_of_a_right_nested_tuple():
    assert [dynamic._nested("s", k, 3) for k in range(3)] == ["s.1", "s.2.1", "s.2.2"]
    assert [dynamic._nested("s", k, 2) for k in range(2)] == ["s.1", "s.2"]
    assert dynamic._nested("s", 0, 1) == "s"


def library(task_id):
    directory = os.path.join(LIBRARY, task_id)
    if not os.path.isdir(directory):
        pytest.skip("library not built")
    return LeanTask.from_dir(directory)


def mutate(task_id, path, new):
    tree = copy.deepcopy(ORACLES[task_id])
    node = tree
    for step in path[:-1]:
        node = node[step]
    node[path[-1]] = new
    return tree


def test_a_wrong_step_is_refused_with_a_run_that_shows_the_invariant_breaking(lean_session):
    task = library("he_003_below_zero")
    wrong = mutate("he_003_below_zero", ["children", 0, "expr"],
                   "(i + 1, bal + operations[i]!, neg || decide (bal + operations[i]! ≤ 0))")      # ≤ where < is meant
    steps = Derivation(task, lean_session).apply_tree(wrong)
    verdict = steps[-1].verdicts[0]
    assert steps[-1].status == "unproved" and verdict.counterexample
    assert "found by running the loop" in verdict.counterexample and "operations := [0]" in verdict.counterexample
    assert "state (i = 0, bal = 0, neg = false)  invariant true" in verdict.counterexample
    assert "the invariant is false after your step" in verdict.counterexample


def test_a_wrong_initial_value_is_caught_before_any_step(lean_session):
    task = library("he_060_sum_to_n")
    wrong = mutate("he_060_sum_to_n", ["init"], ["1", "0"])                                      # i starts at 1 but s = 0
    step = Derivation(task, lean_session).apply_tree(wrong)[0]
    assert step.status == "unproved"
    init = [v for v in step.verdicts if v.obligation.kind == "init"][0]
    assert not init.proved and init.counterexample and "n :=" in init.counterexample


def test_a_correct_loop_has_no_finding(lean_session):
    task = library("he_060_sum_to_n")
    derivation = Derivation(task, lean_session)
    assert all(s.ok for s in derivation.apply_tree(ORACLES["he_060_sum_to_n"]))
    loop = derivation.root
    assert dynamic.loop_finding(derivation, loop.goal, loop.law, "(i + 1, s + (i + 1))") is None


def test_a_harness_that_does_not_elaborate_gives_no_finding_and_no_error(lean_session):
    task = library("he_060_sum_to_n")
    derivation = Derivation(task, lean_session)
    derivation.apply_tree(ORACLES["he_060_sum_to_n"])
    loop = derivation.root
    assert dynamic.loop_finding(derivation, loop.goal, loop.law, "(i + 1, mystery s)") is None
