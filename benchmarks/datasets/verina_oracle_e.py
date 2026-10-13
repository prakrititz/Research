r"""Hand-written derivations for Verina tasks, batch E."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_EO = [{"name": "odd_not_even", "statement": "∀ (n : Int), isOdd n = true → ¬ isEven n = true",
        "proof": "by intro n h h2\n  simp [isOdd, isEven] at h h2\n  omega"},
       {"name": "not_odd_even", "statement": "∀ (n : Int), ¬ isOdd n = true → isEven n = true",
        "proof": "by intro n h\n  simp [isOdd, isEven] at h ⊢\n  omega"},
       {"name": "not_even_odd", "statement": "∀ (n : Int), ¬ isEven n = true → isOdd n = true",
        "proof": "by intro n h\n  simp [isOdd, isEven] at h ⊢\n  omega"}]

_ALLSAME_ARR = [
    {"name": "allsame_arr_pairwise",
     "statement": "∀ (a : Array Int), (∀ k, k < a.size → a[k]! = a[0]!) → List.Pairwise (· = ·) a.toList",
     "proof": "by intro a h\n  apply List.pairwise_of_forall_mem_list\n  intro x hx y hy\n"
              "  obtain ⟨i, hi, rfl⟩ := (Refine.mem_iff_idx a.toList x).mp hx\n"
              "  obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx a.toList y).mp hy\n"
              "  have hi' : i < a.size := by simpa using hi\n  have hj' : j < a.size := by simpa using hj\n"
              "  rw [Refine.toList_getElem_bang a i hi', Refine.toList_getElem_bang a j hj', h i hi', h j hj']"},
    {"name": "allsame_arr_not",
     "statement": "∀ (a : Array Int), 0 < a.size → ¬ (∀ k, k < a.size → a[k]! = a[0]!) → a.toList.any (fun x => decide (x ≠ a.toList[0]!)) = true",
     "proof": "by intro a h0 h\n  push_neg at h\n  obtain ⟨k, hk, hne⟩ := h\n  rw [List.any_eq_true]\n"
              "  have h00 : a.toList[0]! = a[0]! := Refine.toList_getElem_bang a 0 h0\n"
              "  refine ⟨a[k]!, ?_, ?_⟩\n"
              "  · rw [← Refine.toList_getElem_bang a k hk, getElem!_pos a.toList k (by simpa using hk)]; exact List.getElem_mem _\n"
              "  · rw [h00]; simpa using hne"}]

_L024 = [
    {
        "name": "odd_not_even",
        "statement": "∀ (n : Int), isOdd n = true → ¬ isEven n = true",
        "proof": "by\n  intro n h h2\n  simp [isOdd, isEven] at h h2\n  omega"
    },
    {
        "name": "not_odd_even",
        "statement": "∀ (n : Int), ¬ isOdd n = true → isEven n = true",
        "proof": "by\n  intro n h\n  simp [isOdd, isEven] at h ⊢\n  omega"
    },
    {
        "name": "not_even_odd",
        "statement": "∀ (n : Int), ¬ isEven n = true → isOdd n = true",
        "proof": "by\n  intro n h\n  simp [isOdd, isEven] at h ⊢\n  omega"
    },
    {
        "name": "first_even_exit",
        "statement": "∀ (a : Array Int) (n : Nat), (∃ x ∈ a, isEven x = true) → (n ≤ a.size ∧ ∀ k, k < n → isOdd a[k]! = true) → ¬ (n < a.size ∧ isOdd a[n]! = true) → (n < a.size ∧ isEven a[n]! = true ∧ ∀ k, k < n → isOdd a[k]! = true)",
        "proof": "by\n  intro a n hex ⟨hn, hall⟩ hg\n  by_cases h : n < a.size\n  · exact ⟨h, not_odd_even _ (fun ho => hg ⟨h, ho⟩), hall⟩\n  · exfalso\n    obtain ⟨k, hk, hk2⟩ := (Refine.exists_mem_array_iff_idx a (fun y => isEven y = true)).mp hex\n    exact odd_not_even _ (hall k (by omega)) hk2"
    },
    {
        "name": "first_odd_exit",
        "statement": "∀ (a : Array Int) (n : Nat), (∃ x ∈ a, isOdd x = true) → (n ≤ a.size ∧ ∀ k, k < n → isEven a[k]! = true) → ¬ (n < a.size ∧ isEven a[n]! = true) → (n < a.size ∧ isOdd a[n]! = true ∧ ∀ k, k < n → isEven a[k]! = true)",
        "proof": "by\n  intro a n hex ⟨hn, hall⟩ hg\n  by_cases h : n < a.size\n  · exact ⟨h, not_even_odd _ (fun ho => hg ⟨h, ho⟩), hall⟩\n  · exfalso\n    obtain ⟨k, hk, hk2⟩ := (Refine.exists_mem_array_iff_idx a (fun y => isOdd y = true)).mp hex\n    exact odd_not_even _ hk2 (hall k (by omega))"
    }
]

ORACLES_MORE = {
    "verina_basic_69": loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ k, k < n → a[k]! ≠ e", "n < a.size ∧ a[n]! ≠ e",
                            "a.size - n", "n", term("n + 1")),
    "verina_basic_41": with_lemmas(
        loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
             "i ≤ a.size ∧ (ok = true ↔ ∀ k, k < i → a[k]! = a[0]!)", "i < a.size", "a.size - i", "ok",
             term("(i + 1, ok && decide (a[i]! = a[0]!))")), _ALLSAME_ARR),
    "verina_basic_24": with_lemmas(
        bind("ie", "Nat", "ie < a.size ∧ isEven a[ie]! = true ∧ ∀ k, k < ie → isOdd a[k]! = true",
             loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ k, k < n → isOdd a[k]! = true", "n < a.size ∧ isOdd a[n]! = true",
                  "a.size - n", "n", term("n + 1")),
             bind("jo", "Nat", "jo < a.size ∧ isOdd a[jo]! = true ∧ ∀ k, k < jo → isEven a[k]! = true",
                  loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ k, k < n → isEven a[k]! = true", "n < a.size ∧ isEven a[n]! = true",
                       "a.size - n", "n", term("n + 1")),
                  term("a[ie]! - a[jo]!"))),
        _L024),
}
