"""Several obligations, one Lean process: same verdicts, a fraction of the time."""
import time

import pytest

from FormalLLM.llm.parser import parse_expr
from FormalLLM.lspec.parser import parse_spec
from FormalLLM.refinement.frame import obligation_params
from FormalLLM.verification.backends.lean_backend import LeanBackend
from FormalLLM.verification.proof_obligations import ProofObligation

lean = LeanBackend()
needs_lean = pytest.mark.skipif(not lean.available, reason="Lean + Mathlib are not installed")

DECLS = "(N:float)(e:float)(x:float)"


def obligation(pre, post):
    spec = parse_spec(f"Precondition: {DECLS} := true.\nPostcondition: {DECLS} := true.")
    return ProofObligation([parse_expr(pre)], parse_expr(post), params=obligation_params(spec))


GOOD_1 = ("x >= 0 && x * x <= N && e > 0", "x <= x + e")
GOOD_2 = ("N >= 0 && e > 0", "N + e > 0")
BAD = ("x >= 0", "x * x <= 0")                     # false for x = 1


def test_the_batch_theorems_are_named_apart_and_share_one_header():
    first = lean.theorem_text(obligation(*GOOD_1), name="obl_0")
    second = lean.theorem_text(obligation(*GOOD_2), name="obl_1")
    assert "theorem obl_0" in first and "theorem obl_1" in second and "import" not in first


@needs_lean
def test_a_batch_gives_each_obligation_its_own_verdict():
    verdicts = LeanBackend().verify_many([obligation(*GOOD_1), obligation(*BAD), obligation(*GOOD_2)])
    assert [v[0] for v in verdicts] == ["PROVED", "UNKNOWN", "PROVED"]
    assert "did not close this goal" in verdicts[1][1]


@needs_lean
def test_a_batch_costs_about_one_mathlib_load_not_one_per_obligation():
    backend = LeanBackend()
    items = [obligation(*GOOD_1), obligation(*GOOD_2), obligation("x >= 1", "x > 0"),
             obligation("e > 0 && x >= 0", "x + e > 0")]
    started = time.time()
    verdicts = backend.verify_many(items)
    batched = time.time() - started
    assert all(v[0] == "PROVED" for v in verdicts)
    single = LeanBackend()
    started = time.time()
    single.verify(items[0])
    one = time.time() - started
    assert batched < 2.5 * one, f"4 obligations took {batched:.1f}s, one took {one:.1f}s"


@needs_lean
def test_results_are_cached_for_later_single_checks():
    backend = LeanBackend()
    backend.verify_many([obligation(*GOOD_1)])
    before = backend.stats["cached"]
    assert backend.verify(obligation(*GOOD_1))[0] == "PROVED"
    assert backend.stats["cached"] == before + 1


def test_untranslatable_obligations_are_reported_inside_the_batch():
    spec = parse_spec("Precondition: (a:array int)(n:int) := n >= 0.\nPostcondition: (a:array int)(n:int) := true.")
    slice_goal = ProofObligation([parse_expr("n >= 0")], parse_expr("a[0:n] = a[0:n]"),
                                 params=obligation_params(spec))
    verdicts = LeanBackend().verify_many([slice_goal])
    assert verdicts[0][0] == "UNKNOWN" and "not translatable" in verdicts[0][1]
