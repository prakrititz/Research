"""The command line of the Lean core (the parts that need no Lean)."""
import os

import pytest

from FormalLLM.lean.__main__ import main

LIBRARY = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                       "benchmarks", "datasets", "lean_specs")
needs_library = pytest.mark.skipif(not os.path.isdir(os.path.join(LIBRARY, "he_060_sum_to_n")),
                                   reason="library not built: python benchmarks/datasets/lean_specs.py build")


@needs_library
def test_show_prints_the_signature_the_definitions_and_the_root_goal(capsys):
    assert main(["show", os.path.join(LIBRARY, "he_060_sum_to_n")]) == 0
    out = capsys.readouterr().out
    assert "sumToN(n : Nat) : Nat" in out and "def sumToN_postcond" in out and "2 * result = n * (n + 1)" in out
    assert "find ρ : Nat such that sumToN_postcond n ρ h_precond" in out
    assert "-- !benchmark" not in out                                     # region markers are not shown to a reader
    assert "(List.range (n + 1)).sum" not in out                          # nor the reference solution


def test_an_oracle_that_does_not_exist_is_reported_without_starting_lean(capsys):
    assert main(["oracle", "no_such_task"]) == 2
    assert "no hand-written derivation for no_such_task" in capsys.readouterr().out


def test_a_missing_command_is_a_usage_error():
    with pytest.raises(SystemExit):
        main([])
