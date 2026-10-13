r"""Hand-written derivations for Verina tasks, batch J (advanced, family 1 continued: maximum over an enumerated list, with a
case split for the empty input)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import _S28, _S29, _S38, _S44, lemma

_ARGMAX = {
    "name": "argmax_spec",
    "statement": "∀ (n : Nat) (f : Nat → Nat), 0 < n → ∃ i, i < n ∧ f i = ((List.range n).map f).foldl max 0 ∧ "
                 "∀ j, j < n → f j ≤ ((List.range n).map f).foldl max 0",
    "proof": "by intro n f hn\n  have hne : (List.range n).map f ≠ [] := List.ne_nil_of_mem (a := f 0) "
             "(List.mem_map.mpr ⟨0, List.mem_range.mpr hn, rfl⟩)\n"
             "  obtain ⟨h1, h2⟩ := Refine.maxlist_nat _ hne\n"
             "  rw [List.contains_iff_mem, List.mem_map] at h1\n  obtain ⟨i, hi, hfi⟩ := h1\n"
             "  refine ⟨i, List.mem_range.mp hi, hfi, ?_⟩\n  intro j hj\n"
             "  have := List.all_eq_true.mp h2 (f j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)\n  simpa using this"}

_E44 = _S44 + "subarraySums.foldl max (subarraySums.headD 0)"
_C44 = _S44 + "subarraySums.length = 0"
_E29 = _S29 + "(validSubArrays.map (·.length)).foldl max 0"
_E28 = _S28 + "consec_sublist_lens.foldl max 0"
_BIND44 = "intro subarrays divisibleSubarrays subarraySums\n  "

ORACLES_MORE = {
    "verina_advanced_44": cases(
        f"({_C44})",
        with_lemmas(term("0"), [lemma("sl44_nil", "maxSubarraySumDivisibleByK", "(arr : Array Int) (k : Int)", ["arr", "k"], "0",
                                      _BIND44 + "have hx' : subarraySums.length = 0 := hx\n  "
                                      "exact ⟨fun _ => rfl, fun hpos => by omega⟩", hyp=f"({_C44})", no_precond=True)]),
        with_lemmas(term(f"({_E44})"), [lemma("sl44_ne", "maxSubarraySumDivisibleByK", "(arr : Array Int) (k : Int)", ["arr", "k"], _E44,
                                              _BIND44 + "have hx' : ¬ subarraySums.length = 0 := hx\n  "
                                              "have hne : subarraySums ≠ [] := fun e => hx' (by simp [e])\n  "
                                              "obtain ⟨h1, h2⟩ := Refine.maxlist_int subarraySums hne\n  "
                                              "exact ⟨fun h0 => absurd h0 hx', fun _ => ⟨List.contains_iff_mem.mp h1, h2⟩⟩",
                                              hyp=f"¬ ({_C44})", no_precond=True)])),
    "verina_advanced_29": cases(
        "nums = []",
        with_lemmas(term("0"), [lemma("lg29_nil", "longestGoodSubarray", "(nums : List Nat) (k : Nat)", ["nums", "k"], "0",
                                      "exact Or.inl ⟨hx, rfl⟩", hyp="nums = []")]),
        with_lemmas(term(f"({_E29})"), [lemma("lg29_ne", "longestGoodSubarray", "(nums : List Nat) (k : Nat)", ["nums", "k"], _E29,
                                              "intro subArrays subArrayFreqs validSubArrays\n  "
                                              "have hnil : [] ∈ validSubArrays := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(nums.drop 0).take 0, "
                                              "List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by omega), "
                                              "List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩⟩, by simp⟩, by simp⟩\n  "
                                              "exact Or.inr ⟨hx, Refine.maxlen_spec validSubArrays hnil⟩", hyp="¬ nums = []")])),
    "verina_advanced_28": cases(
        "nums = []",
        with_lemmas(term("0"), [lemma("lc28_nil", "longestConsecutive", "(nums : List Int)", ["nums"], "0",
                                      "exact ⟨fun _ => rfl, fun hne => absurd hx hne⟩", hyp="nums = []")]),
        with_lemmas(term(f"({_E28})"), [lemma("lc28_ne", "longestConsecutive", "(nums : List Int)", ["nums"], _E28,
                                              "intro sorted_nums consec_sublist_lens\n  "
                                              "have hne : consec_sublist_lens ≠ [] := List.ne_nil_of_mem (a := 0) "
                                              "(List.mem_map.mpr ⟨sorted_nums.extract 0 0, List.mem_filter.mpr ⟨List.mem_flatMap.mpr "
                                              "⟨0, List.mem_range.mpr (List.length_pos_of_ne_nil hx), "
                                              "List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩⟩, by simp [isConsecutive]⟩, by simp⟩)\n  "
                                              "exact ⟨fun h0 => absurd h0 hx, fun _ => Refine.maxlist_nat _ hne⟩", hyp="¬ nums = []")])),
    "verina_advanced_38": with_lemmas(
        term(f"((List.range intervals.length).map {_S38}).foldl max 0"),
        [_ARGMAX, lemma("mc38", "maxCoverageAfterRemovingOne", "(intervals : List (Prod Nat Nat))", ["intervals"],
                        f"((List.range intervals.length).map {_S38}).foldl max 0",
                        f"obtain ⟨i, hi, he, hall⟩ := argmax_spec intervals.length {_S38} h\n  "
                        "exact ⟨i, hi, he.symm, fun j hj => le_of_le_of_eq (hall j hj) he.symm⟩")]),
}
