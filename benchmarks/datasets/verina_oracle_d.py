r"""Hand-written derivations for Verina tasks, batch D (searches with exit lemmas, flags over arrays, sorting)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_FOLDMAX = {"name": "foldl_max_nat",
            "statement": "∀ (l : List Nat) (m : Nat), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ "
                         "∀ x ∈ l, x ≤ List.foldl max m l",
            "proof": "by intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n"
                     "    obtain ⟨h1, h2, h3⟩ := ih (max m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n"
                     "    · rcases h1 with h | h\n      · by_cases hm : m ≤ a\n        · right; rw [max_eq_right hm] at h ⊢; rw [h]; simp\n"
                     "        · left\n          have hmx : max m a = m := max_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n"
                     "      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans (le_max_left m a) h2\n"
                     "    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans (le_max_right m x) h2\n"
                     "      · exact h3 x hx'"}

ORACLES_MORE = {
    "verina_basic_33": with_lemmas(
        loop([["v", "Nat"]], ["0"], "∀ k, k < v → List.elem k s = true", "List.elem v s = true", "s.foldl max 0 + 1 - v", "v",
             term("v + 1")),
        [_FOLDMAX, {"name": "elem_le_max", "statement": "∀ (s : List Nat) (v : Nat), List.elem v s = true → v ≤ s.foldl max 0",
                    "proof": "by intro s v h\n  have hm : v ∈ s := by simpa using h\n  obtain ⟨_, _, h3⟩ := foldl_max_nat s 0\n  exact h3 v hm"}]),
    "verina_basic_45": with_lemmas(
        term("match firstEvenOddIndices lst with | some (ei, oi) => lst[ei]! * lst[oi]! | none => 0"),
        [{"name": "findproduct_post",
          "statement": "∀ (lst : List Int) (h : findProduct_precond lst), findProduct_postcond lst "
                       "(match firstEvenOddIndices lst with | some (ei, oi) => lst[ei]! * lst[oi]! | none => 0) h",
          "proof": "by intro lst h\n  unfold findProduct_postcond\n  cases hf : firstEvenOddIndices lst with\n  | none => simp\n"
                   "  | some p => obtain ⟨a, b⟩ := p; simp"}]),
    "verina_basic_49": bind(
        "p", "Nat", "p ≤ a.size ∧ (∀ j, j < p → ¬ isOdd a[j]! = true) ∧ (p < a.size → isOdd a[p]! = true)",
        loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ j, j < n → ¬ isOdd a[j]! = true", "n < a.size ∧ ¬ isOdd a[n]! = true",
             "a.size - n", "n", term("n + 1")),
        cases("p < a.size", term("some p"), term("none"))),
    "verina_basic_9": loop(
        [["i", "Nat"], ["f", "Bool"]], ["0", "false"],
        "i ≤ a.size ∧ (f = true ↔ ∃ k, k < i ∧ ∃ j, j < b.size ∧ a[k]! = b[j]!)", "i < a.size", "a.size - i", "f",
        bind("hit", "Bool", "hit = true ↔ ∃ j, j < b.size ∧ a[i]! = b[j]!",
             loop([["j", "Nat"], ["g", "Bool"]], ["0", "false"], "j ≤ b.size ∧ (g = true ↔ ∃ m, m < j ∧ a[i]! = b[m]!)",
                  "j < b.size", "b.size - j", "g", term("(j + 1, g || decide (a[i]! = b[j]!))")),
             term("(i + 1, f || hit)"))),
    "verina_basic_87": with_lemmas(
        term("(a.toList.mergeSort (fun x y => decide (x ≤ y))).toArray"),
        [{"name": "sort_array_ok",
          "statement": "∀ (l : List Int), List.Pairwise (· ≤ ·) ((l.mergeSort (fun x y => decide (x ≤ y))).toArray.toList) ∧ "
                       "List.isPerm l ((l.mergeSort (fun x y => decide (x ≤ y))).toArray.toList) = true",
          "proof": "by intro l\n  have hp : (l.mergeSort (fun x y => decide (x ≤ y))).Perm l := List.mergeSort_perm l _\n"
                   "  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (l.mergeSort (fun x y => decide (x ≤ y))) :=\n"
                   "    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) l\n"
                   "  refine ⟨?_, ?_⟩\n  · simpa using hs\n  · simpa using List.isPerm_iff.mpr hp.symm"}]),
}
