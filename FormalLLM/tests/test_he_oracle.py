"""The hand-written derivations of the HumanEval pilot problems are derivations (engine-checked) and run on the real tests."""
import os
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

he = pytest.importorskip("benchmarks.datasets.humaneval")
pytestmark = pytest.mark.skipif(not he.EVALPLUS_AVAILABLE, reason="evalplus is not installed")

from benchmarks.datasets import he_oracle, he_specs                      # noqa: E402

FAST = ["HumanEval/41", "HumanEval/157", "HumanEval/138", "HumanEval/60", "HumanEval/102", "HumanEval/52",
        "HumanEval/35", "HumanEval/24", "HumanEval/53", "HumanEval/45", "HumanEval/97", "HumanEval/150",
        "HumanEval/135", "HumanEval/57"]
SLOW = ["HumanEval/13", "HumanEval/31", "HumanEval/77"]


@pytest.mark.parametrize("task", FAST)
def test_a_hand_derivation_is_accepted_step_by_step_and_passes_every_test(task):
    row = he_oracle.check(task)
    assert row["complete"], row["error"]
    assert row["base"] == "pass" and row["plus"] == "pass"


@pytest.mark.parametrize("task", SLOW)
def test_three_derivations_are_proved_correct_but_too_slow_for_the_largest_inputs(task):
    # a downward search for a divisor, trial division up to n, or a search for a cube root is right but cannot
    # finish on EvalPlus' largest inputs: correctness proved, efficiency not part of the specification
    row = he_oracle.check(task)
    assert row["complete"], row["error"]
    assert row["base"] == "pass" and row["plus"] in ("pass", "timeout")


def test_the_problems_without_a_derivation_are_the_ones_that_were_not_attempted():
    # all three are searches over pairs or triples of positions (two or three nested loops)
    assert set(he_specs.SPECS) - set(he_oracle.ORACLE) == {"HumanEval/0", "HumanEval/43", "HumanEval/40"}
    assert set(he_oracle.ORACLE) <= set(he_specs.SPECS)
