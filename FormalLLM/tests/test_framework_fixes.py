"""The framework fixes of 2026-10-26 that need no Lean: reply checks, stop conditions, prompt pieces, retrieval."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from FormalLLM.lean import agent
from FormalLLM.lean.agent import LeanAgent, _PROOF_IN_VALUE
from FormalLLM.llm.transport import ENDPOINT_CUTOFF_MARKS


def cutoff(message):
    return any(mark in message for mark in ENDPOINT_CUTOFF_MARKS)


def test_proof_in_a_value_is_caught():
    for proof in ["by\n  refine ⟨x, ?_⟩\n  simp", "⟨String.ofList l, by simp⟩", "Exists.intro a (by simp)", "f ?_"]:
        assert _PROOF_IN_VALUE.search(proof), proof


def test_plain_values_are_not_flagged():
    for value in ["Nat.primeFactorsList n", "(i + 1, acc ++ [x])", "⟨a, b⟩", "(⟨i, h⟩ : Fin n)",
                  "if a ∈ l then 1 else 0", "∃ k, k < n ∧ P k", "l.foldl (fun acc x => acc + x) 0"]:
        assert not _PROOF_IN_VALUE.search(value), value


def test_dead_model_key_quota_and_cap_stop_the_run():
    assert cutoff('https://api.openai.com/v1 returned HTTP 404: {"error": {"code": "model_not_found"}}')
    assert cutoff("The model `o3-mini` has been deprecated")
    assert cutoff("https://api.openai.com/v1 returned HTTP 401: invalid_api_key")
    assert cutoff("Global budget ceiling reached ($8.01 >= $8.00)")


def test_an_ordinary_bad_request_does_not_stop_the_run():
    assert not cutoff("https://api.openai.com/v1 returned HTTP 400: bad request")
    assert not cutoff("the term step is not accepted")


def test_binder_names():
    names = LeanAgent._binder_names("(numbers : List Int) (d : Int) (h_precond : f_precond numbers d) (i acc : Nat) "
                                    "(hinv : (fun (i : Nat) => i ≤ 3) i)")
    assert names == ["numbers", "d", "h_precond", "i", "acc", "hinv"]
    assert LeanAgent._binder_names("{α : Type} (l : List α)") is None


def test_name_hints_prefer_definitions_containing_the_word():
    a = LeanAgent(None)
    a._ns_cache = {"List": ["sort_append", "mergeSort", "insertionSort", "or", "insert", "sortedLT_append", "instFoo"]}
    hint = a._name_hints(object(), "The environment does not contain `List.sort`, so")
    assert "`List.mergeSort`" in hint and "sort_append" not in hint and "instFoo" not in hint


def test_library_card_lists_proved_lemmas():
    card = agent.library_card()
    assert "Refine.forall_mem_iff_idx" in card and card.count("\n") > 20


def test_retrieval_never_shows_the_same_benchmark():
    from FormalLLM.lean import retrieval
    shown = retrieval.examples("he_003_below_zero", "def belowZero_postcond (operations : List Int) (result : Bool) := result = true")
    assert shown and all(s.startswith("Worked example (verina_") for s in shown)
    shown = retrieval.examples("verina_basic_10", "def f_postcond (a : Array Int) (n : Int) (result : Bool) := True")
    assert shown and not any(s.startswith("Worked example (verina_") for s in shown)
