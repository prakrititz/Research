r"""Hand-written derivations for Verina tasks, batch AB (corrections: the one task of the first batch that was still incomplete)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import lemma

ORACLES_MORE = {
    # the k-th element: the specification asks for a member of the array that equals arr[k-1]; the witness is arr[k-1] itself
    "verina_basic_4": with_lemmas(
        term("arr[k - 1]!"),
        [lemma("kth4", "kthElement", "(arr : Array Int) (k : Nat)", ["arr", "k"], "arr[k - 1]!",
               "rw [← Array.any_toList, List.any_eq_true]\n  obtain ⟨hk1, hk2⟩ := h\n"
               "  refine ⟨arr[k - 1]!, ?_, by simp⟩\n"
               "  rw [← Refine.toList_getElem_bang arr (k - 1) (by omega)]\n"
               "  exact Refine.getElem_bang_mem arr.toList (k - 1) (by simpa using (by omega : k - 1 < arr.size))")]),
}
