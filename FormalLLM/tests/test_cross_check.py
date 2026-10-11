"""The model-free cross-check must be able to *fail*: wrong and runaway programs are caught."""
import os
import random
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "benchmarks"))

import cross_check as cc                                              # noqa: E402

RNG = random.Random(1)
SQRT_OK = "x = 0\nwhile (N >= ((x + e) * (x + e))):\n    x = (x + e)\n"


def verdict(case_id, code, extra=0):
    n, spec_bad, base_bad, runaway = cc.check_program(case_id, code, extra, RNG)
    return n, len(spec_bad), len(base_bad), len(runaway)


def test_the_papers_square_root_program_passes_every_input():
    n, spec_bad, base_bad, runaway = verdict("C5-sqrt-paper", SQRT_OK, extra=30)
    assert n == 12 + 30 and (spec_bad, base_bad, runaway) == (0, 0, 0)


def test_a_wrong_program_is_caught_by_both_checks():
    n, spec_bad, base_bad, runaway = verdict("C5-sqrt-paper", "x = 0\n")        # never moves
    assert spec_bad > 0 and base_bad > 0 and runaway == 0


def test_a_loop_that_never_stops_is_reported_not_hung():
    n, spec_bad, base_bad, runaway = verdict("C5-sqrt-paper", "x = 0\nwhile (e > 0):\n    x = (x + e)\n")
    assert runaway == n


def test_multi_output_cases_use_the_frame_order():
    # D1 returns (q, r): a swapped pair must fail, the right one pass
    good = "q = 0\nr = n\nwhile (r >= d):\n    r = (r - d)\n    q = (q + 1)\n"
    bad = "q = n\nr = 0\n"
    assert verdict("D1-intdiv", good, extra=20)[1:] == (0, 0, 0)
    assert verdict("D1-intdiv", bad)[1] > 0


def test_frame_order_and_signature_parsing():
    assert cc.frame_order("Frame: s, d.\nPrecondition: ...") == ["s", "d"]
    assert cc.frame_order("Frame: q:int, r:int.\n") == ["q", "r"]
    assert cc.signature_params("def f(N: float, e: float) -> float:") == ["N", "e"]


C3_SPEC = "Frame: i.\nPrecondition: (N:int)(i:int) := N >= 0 /\\ i = 0.\nPostcondition: (N:int)(i:int) := i >= N."


def test_a_start_value_pinned_by_the_precondition_is_supplied():
    # C3 says i starts at 0 but the baseline's signature has no i, so the checker reads it from the spec
    assert cc.pinned_initials(C3_SPEC, ["N"], ["i"]) == {"i": 0}
    assert cc.pinned_initials(C3_SPEC, ["N", "i"], ["i"]) == {}                 # already passed in
    assert cc.pinned_initials("Frame: x.\nPrecondition: (N:float) := N >= 0.\nPostcondition: x >= 0.",
                              ["N"], ["x"]) == {}
    # a loop that reads i and an assignment that ignores it both pass; a wrong program is still caught
    assert verdict("C3-loop-pinned", "while (i < N):\n    i = (i + 1)\n")[1:] == (0, 0, 0)
    assert verdict("C3-loop-pinned", "i = N\n")[1:] == (0, 0, 0)
    assert verdict("C3-loop-pinned", "i = 0\n")[1] > 0


def test_a_program_that_crashes_is_reported_not_fatal():
    n, spec_bad, base_bad, runaway = verdict("C3-loop-pinned", "i = no_such_name\n")
    assert spec_bad == n and base_bad == n and runaway == 0
