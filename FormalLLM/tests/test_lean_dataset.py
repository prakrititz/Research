"""One interface for Verina and HumanEval: the registry, the input encodings, and the shared evaluator.

The tests that need Lean skip themselves when the toolchain (or the Verina clone) is not installed."""
import os

import pytest

from FormalLLM.lean import dataset as datasets
from FormalLLM.lean.evaluate import candidate_source, ground_truth_code, task_source
from FormalLLM.lean.task import LeanTask, lean_char, render


def test_registry_knows_the_four_names_and_resolves_ids_by_prefix():
    assert set(datasets.names()) >= {"verina", "humaneval", "classic", "lean_specs"}
    assert datasets.resolve("verina_basic_5").name == "verina"
    assert datasets.resolve("he_060_sum_to_n").name == "humaneval"
    assert datasets.resolve("classic_isqrt").name == "classic"
    with pytest.raises(KeyError):
        datasets.resolve("nothing_here")
    with pytest.raises(KeyError):
        datasets.get("mbpp")


def test_our_datasets_partition_the_library():
    he, classic, both = (datasets.get(n) for n in ("humaneval", "classic", "lean_specs"))
    assert len(he.ids()) == 164 and len(classic.ids()) == 5
    assert set(both.ids()) == set(he.ids()) | set(classic.ids())
    assert all(i.startswith("he_") for i in he.ids())


def test_every_oracle_belongs_to_its_dataset_and_to_an_existing_task():
    for name in ("humaneval", "classic", "verina"):
        ds = datasets.get(name)
        if not ds.ids():
            continue
        table = ds.oracles()
        assert table and set(table) <= set(ds.ids()), name


def test_inputs_are_read_by_the_encoding_of_their_dataset():
    ours = datasets.get("humaneval").load("he_142_sum_squares")
    assert ours.encoding == "lean" and ours.call_args(ours.tests[0]) == f"({ours.tests[0]['input']['lst']})"
    assert render(",", "Char") == "','" and lean_char("'") == "'\\''"
    assert render("a b", "String") == '"a b"' and render([1, -2], "Array Int") == "#[1, (-2)]"


@pytest.mark.skipif(not datasets.get("verina").ids(), reason="Verina is not cloned into ~/.formalllm/verina")
def test_verina_json_inputs_become_lean_literals():
    task = datasets.get("verina").load("verina_basic_38")           # a String parameter: the JSON value is the raw text
    case = task.tests[0]
    assert task.encoding == "json" and task.call_args(case) == f'("{case["input"]["s"]}")'
    assert datasets.get("verina").compat.strip() != ""


def test_both_datasets_have_the_same_file_regions():
    for name, task_id in (("humaneval", "he_142_sum_squares"), ("verina", "verina_basic_5")):
        ds = datasets.get(name)
        if task_id not in ds.ids():
            continue
        task = ds.load(task_id)
        text = task_source(task)
        for region in ("code", "postcond", "precond", "proof"):
            assert f"@start {region}" in text and f"@end {region}" in text, (name, region)
        swapped = candidate_source(text, "  sorry")
        from FormalLLM.lean.task import CODE
        assert CODE.search(swapped).group(2).strip() == "sorry" and ground_truth_code(text).strip() != "sorry"
        assert not any(l.lstrip().startswith("import ") for l in swapped.splitlines())


def test_a_reference_scores_the_same_way_on_both_datasets():
    from FormalLLM.lean.evaluate import score_code, solved
    from FormalLLM.lean.session import LeanSession, LeanUnavailable
    try:
        lean = LeanSession(imports="import Mathlib", startup_timeout=900)
    except LeanUnavailable:
        pytest.skip("Lean is not installed")
    with lean:
        for name, task_id in (("humaneval", "he_060_sum_to_n"), ("verina", "verina_basic_5")):
            ds = datasets.get(name)
            if task_id not in ds.ids():
                continue
            result = score_code(lean, ds.load(task_id))
            assert solved(result), (name, result)
