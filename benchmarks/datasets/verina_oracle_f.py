r"""Hand-written derivations for Verina tasks, batch F (advanced: decidable restatements, sorting, simple searches)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_LE = "(fun a b => decide (a ≤ b))"
_SORT = [{"name": "sorted_perm",
          "statement": f"∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort {_LE}) ∧ List.isPerm l (l.mergeSort {_LE}) = true",
          "proof": "by intro l\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) l, List.isPerm_iff.mpr (List.mergeSort_perm l _).symm⟩"}]
_SORT_REV = [{"name": "sorted_perm_rev",
              "statement": f"∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort {_LE}) ∧ List.isPerm (l.mergeSort {_LE}) l = true",
              "proof": "by intro l\n  exact ⟨List.pairwise_mergeSort' (· ≤ ·) l, List.isPerm_iff.mpr (List.mergeSort_perm l _)⟩"}]
_SORT_NAT_ARR = [{"name": "sorted_perm_arr",
                  "statement": "∀ (l : List Nat), List.Pairwise (· ≤ ·) ((l.mergeSort (fun a b => decide (a ≤ b))).toArray.toList) ∧ "
                               "(((l.mergeSort (fun a b => decide (a ≤ b))).toArray.toList).isPerm l) = true",
                  "proof": "by intro l\n  have hp : (l.mergeSort (fun a b => decide (a ≤ b))).Perm l := List.mergeSort_perm l _\n"
                           "  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (l.mergeSort (fun a b => decide (a ≤ b))) :=\n"
                           "    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) l\n"
                           "  refine ⟨?_, ?_⟩\n  · simpa using hs\n  · simpa using List.isPerm_iff.mpr hp"}]
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
    "verina_advanced_18": term("decide (n = List.foldl (fun acc d => acc + d ^ countDigits n) 0 "
                               "(List.map (fun c => c.toNat - '0'.toNat) (toString n).toList))"),
    "verina_advanced_19": term("decide (normalizeString s = (normalizeString s).reverse)"),
    "verina_advanced_21": term("s.toList == s.toList.reverse"),
    "verina_advanced_59": term("decide ((s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower) = "
                               "(s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower).reverse)"),
    "verina_advanced_6": term("['a', 'e', 'i', 'o', 'u'].all (fun v => (normalize_str s).contains v)"),
    "verina_advanced_60": term("(nums.filter (fun n => n % 2 == 0), nums.filter (fun n => n % 2 == 1))"),
    "verina_advanced_65": term("String.mk s.toList.reverse"),
    "verina_advanced_7": term("List.foldl (fun acc bit => acc * 2 + bit) 0 digits"),
    "verina_advanced_9": term("(List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)).length"),
    "verina_advanced_63": term("nums.eraseDups.length"),
    "verina_advanced_72": cases("n = 0", term("0"), cases("n % 2 = 0", term("2"), cases("n % 3 = 0", term("3"),
                                cases("n % 5 = 0", term("5"), cases("n % 7 = 0", term("7"), term("0")))))),
    "verina_advanced_81": with_lemmas(term(f"arr.eraseDups.mergeSort {_LE}"), _SORT),
    "verina_advanced_48": with_lemmas(term(f"list.mergeSort {_LE}"), _SORT),
    "verina_advanced_49": with_lemmas(term(f"(arr1 ++ arr2).mergeSort {_LE}"), _SORT),
    "verina_advanced_51": with_lemmas(term(f"(a ++ b).mergeSort {_LE}"), _SORT_REV),
    "verina_advanced_70": cases("nums.idxOf 1 > nums.idxOf (Int.ofNat nums.length)",
                                term("(nums.idxOf 1 : Int) + (nums.length : Int) - 2 - (nums.idxOf (Int.ofNat nums.length) : Int)"),
                                term("(nums.idxOf 1 : Int) + (nums.length : Int) - 1 - (nums.idxOf (Int.ofNat nums.length) : Int)")),
    "verina_advanced_77": term("((List.range height.length).map (fun i => Nat.min (List.take (i + 1) height |>.foldl Nat.max 0) "
                               "(List.drop i height |>.foldl Nat.max 0) - height[i]!)).foldl (· + ·) 0"),
    "verina_advanced_73": with_lemmas(
        loop([["v", "Nat"]], ["0"], "∀ k, k < v → k ∈ l", "v ∈ l", "l.foldl max 0 + 1 - v", "v", term("v + 1")),
        [_FOLDMAX, {"name": "mem_le_max", "statement": "∀ (s : List Nat) (v : Nat), v ∈ s → v ≤ s.foldl max 0",
                    "proof": "by intro s v h\n  obtain ⟨_, _, h3⟩ := foldl_max_nat s 0\n  exact h3 v h"}]),
    "verina_advanced_69": loop([["n", "Nat"]], ["0"], "n ≤ xs.length ∧ ∀ i, i < n → xs[i]! < target", "n < xs.length ∧ xs[n]! < target",
                               "xs.length - n", "n", term("n + 1")),
}
