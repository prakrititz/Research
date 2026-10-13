r"""Hand-written derivations for Verina tasks, batch L (advanced: sorting, filtering, brute-force decisions)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import lemma

_P11 = "fun x => decide ((lst.filter (fun y => y = x)).length > lst.length / 2)"
_MAJ11 = {
    "name": "maj11",
    "statement": "∀ (lst : List Int) (h : findMajorityElement_precond lst) (res : Int), "
                 "(((∀ x, x ∈ lst → (lst.filter (fun y => y = x)).length ≤ lst.length / 2) ∧ res = -1) ∨ "
                 "(lst.filter (fun y => y = res)).length > lst.length / 2) → findMajorityElement_postcond lst res h",
    "proof": "by intro lst h res hc\n  unfold findMajorityElement_postcond\n  dsimp only\n"
             "  rcases hc with ⟨hall, hres⟩ | hmaj\n"
             "  · exact ⟨fun _ => Or.inl (List.all_eq_true.mpr fun x hx => by simpa using hall x hx), fun hne => absurd hres hne⟩\n"
             "  · have hmaj' : (lst.filter (fun y => y = res)).length > lst.length / 2 ∧ "
             "lst.all (fun x => decide ((lst.filter (fun y => y = x)).length ≤ lst.length / 2 ∨ x = res)) = true := by\n"
             "      refine ⟨hmaj, List.all_eq_true.mpr fun x hx => ?_⟩\n      by_cases hxr : x = res\n      · simp [hxr]\n"
             "      · have := Refine.filter_pair_le lst x res hxr\n        simp only [decide_eq_true_eq]; left; omega\n"
             "    exact ⟨fun _ => Or.inr hmaj', fun _ => hmaj'⟩"}
_FIND11 = {
    "name": "find11",
    "statement": "∀ (lst : List Int) (h : findMajorityElement_precond lst), findMajorityElement_postcond lst "
                 f"((lst.find? ({_P11})).getD (-1)) h",
    "proof": "by intro lst h\n  apply maj11 lst h\n  cases hf : lst.find? (" + _P11 + ") with\n"
             "  | none =>\n    left\n    refine ⟨?_, rfl⟩\n    intro x hx\n    have := List.find?_eq_none.mp hf x hx\n"
             "    simpa using this\n"
             "  | some r =>\n    right\n    simp only [Option.getD_some]\n    have hp := List.find?_some hf\n    simp only [decide_eq_true_eq] at hp\n    exact hp"}

_SORTI = {
    "name": "sorted_perm_nat_arr",
    "statement": "∀ (l : List Nat), List.Pairwise (· ≤ ·) ((l.mergeSort (fun a b => decide (a ≤ b))).toArray.toList) ∧ "
                 "((l.mergeSort (fun a b => decide (a ≤ b))).toArray.toList).isPerm l = true",
    "proof": "by intro l\n  rw [List.toList_toArray]\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) l, List.isPerm_iff.mpr (List.mergeSort_perm l _)⟩"}

ORACLES_MORE = {
    "verina_advanced_11": with_lemmas(term(f"(lst.find? ({_P11})).getD (-1)"), [_MAJ11, _FIND11]),
    "verina_advanced_26": with_lemmas(
        term("if digits.isEmpty then [] else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then [] "
             "else digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [\"\"]"),
        [lemma("lc26", "letterCombinations", "(digits : String)", ["digits"],
               "if digits.isEmpty then [] else if digits.toList.any (λ c => ¬(c ∈ ['2','3','4','5','6','7','8','9'])) then [] "
               "else digits.toList.map digitToLetters |>.foldl (λ acc ls => acc.flatMap (λ s => ls.map (λ c => s ++ String.singleton c)) ) [\"\"]",
               "split_ifs <;> simp_all")]),
    "verina_advanced_50": with_lemmas(
        term("((a1.toList ++ a2.toList).mergeSort (fun x y => decide (x ≤ y))).toArray"),
        [lemma("ms50", "mergeSorted", "(a1 a2 : Array Nat)", ["a1", "a2"], "((a1.toList ++ a2.toList).mergeSort (fun x y => decide (x ≤ y))).toArray",
               "rw [List.toList_toArray]\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) _, List.isPerm_iff.mpr (List.mergeSort_perm _ _)⟩")]),
    "verina_advanced_64": with_lemmas(
        term("lst.filter (fun x => decide (x ≠ target))"),
        [lemma("rm64", "removeElement", "(lst : List Nat) (target : Nat)", ["lst", "target"], "lst.filter (fun x => decide (x ≠ target))",
               "dsimp only\n  refine ⟨?_, rfl⟩\n  rw [List.all_eq_true]\n  rintro ⟨x, i⟩ hx\n"
               "  have := (List.mem_zipIdx_iff_getElem?.mp hx)\n  simp only at this\n  rw [this]\n  simp")]),
}
