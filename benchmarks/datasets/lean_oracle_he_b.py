r"""Hand-written derivations for HumanEval problems that needed a heavier invariant or a lemma (batch file B)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_ROLL = [
    {
        "name": "foldl_max_facts",
        "statement": "∀ (l : List Int) (m : Int), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l",
        "proof": "by\n  intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n    obtain ⟨h1, h2, h3⟩ := ih (max m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n    · rcases h1 with h | h\n      · by_cases hm : m ≤ a\n        · right; rw [max_eq_right hm] at h ⊢; rw [h]; simp\n        · left\n          have hmx : max m a = m := max_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans (le_max_left m a) h2\n    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans (le_max_right m x) h2\n      · exact h3 x hx'"
    },
    {
        "name": "rolling_ok",
        "statement": "∀ (numbers : List Int), ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)).length = numbers.length ∧ ∀ i, i < numbers.length → ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]!",
        "proof": "by\n  intro numbers\n  refine ⟨by simp, ?_⟩\n  intro i hi\n  have hget : ((List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!))[i]! =\n      (numbers.take (i + 1)).foldl max numbers[0]! := by\n    rw [getElem!_pos _ i (by simpa using hi)]\n    simp\n  rw [hget]\n  obtain ⟨h1, h2, h3⟩ := foldl_max_facts (numbers.take (i + 1)) numbers[0]!\n  refine ⟨?_, h3⟩\n  rcases h1 with h | h\n  · rw [h]\n    have : numbers[0]! ∈ numbers.take (i + 1) := by\n      rw [getElem!_pos numbers 0 (by omega)]\n      exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩\n    exact this\n  · exact h"
    }
]
_INTER = [
    {
        "name": "append_pair_idx",
        "statement": "∀ (a : List Int) (d x : Int) (j : Nat), (a ++ [d, x])[j]! = (if j < a.length then a[j]! else if j = a.length then d else if j = a.length + 1 then x else default)",
        "proof": "by\n  intro a d x j\n  by_cases h : j < a.length\n  · rw [if_pos h]; exact Refine.getElem_bang_append_lt a [d, x] j h\n  · rw [if_neg h]\n    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega : a.length ≤ j)]\n    by_cases h2 : j = a.length\n    · subst h2; simp\n    · rw [if_neg h2]\n      by_cases h3 : j = a.length + 1\n      · subst h3; simp\n      · rw [if_neg h3]\n        have : j - a.length ≥ 2 := by omega\n        simp [List.getElem?_eq_none (by simp; omega : [d, x].length ≤ j - a.length)]"
    }
]

_SORT116 = [
    {
        "name": "sort116_ok",
        "statement": "∀ (L : List Int), (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).length - 1 → (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! < ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∨ (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! = ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∧ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! ≤ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]!))",
        "proof": "by\n  intro L\n  have htrans : ∀ (a b c : Int), (decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))) = true →\n      (decide (ones b < ones c) || (ones b == ones c && decide (b ≤ c))) = true →\n      (decide (ones a < ones c) || (ones a == ones c && decide (a ≤ c))) = true := by\n    intro a b c h1 h2\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *\n    omega\n  have htotal : ∀ (a b : Int), ((decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))) ||\n      (decide (ones b < ones a) || (ones b == ones a && decide (b ≤ a)))) = true := by\n    intro a b\n    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]\n    omega\n  have hp : (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).Perm L :=\n    List.mergeSort_perm L _\n  have hs := List.pairwise_mergeSort htrans htotal L\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] using this"
    }
]
_SORT_NAT_ASC = [
    {
        "name": "sortNat_ok",
        "statement": "∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!",
        "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≤ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (L.mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≤ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
    }
]
_SORT_NAT_DESC = [
    {
        "name": "sortNatDesc_ok",
        "statement": "∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≥ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≥ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (L.mergeSort (fun a b => decide (a ≥ b)))[i + 1]!",
        "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≥ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≥ b) = true) (L.mergeSort (fun a b => decide (a ≥ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≥ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
    }
]

_MINSUB = [
    {
        "name": "foldl_min_facts",
        "statement": "∀ (l : List Int) (m : Int), (List.foldl min m l = m ∨ List.foldl min m l ∈ l) ∧ List.foldl min m l ≤ m ∧ ∀ x ∈ l, List.foldl min m l ≤ x",
        "proof": "by\n  intro l\n  induction l with\n  | nil => intro m; simp\n  | cons a t ih =>\n    intro m\n    obtain ⟨h1, h2, h3⟩ := ih (min m a)\n    simp only [List.foldl_cons]\n    refine ⟨?_, ?_, ?_⟩\n    · rcases h1 with h | h\n      · by_cases hm : a ≤ m\n        · right; rw [min_eq_right hm] at h ⊢; rw [h]; simp\n        · left\n          have hmx : min m a = m := min_eq_left (by omega)\n          rw [hmx] at h ⊢; exact h\n      · right; exact List.mem_cons_of_mem a h\n    · exact le_trans h2 (min_le_left m a)\n    · intro x hx\n      rcases List.mem_cons.mp hx with rfl | hx'\n      · exact le_trans h2 (min_le_right m x)\n      · exact h3 x hx'"
    },
    {
        "name": "minsub_ok",
        "statement": "∀ (nums : List Int), nums ≠ [] → (∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum))) ≤ ((nums.drop i).take (j - i)).sum",
        "proof": "by\n  intro nums hne\n  obtain ⟨h1, h2, h3⟩ := foldl_min_facts ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum))) nums[0]!\n  refine ⟨?_, ?_⟩\n  · rcases h1 with h | h\n    · have hlen : 0 < nums.length := List.length_pos_iff.mpr hne\n      refine ⟨1, by omega, 0, by omega, ?_⟩\n      rw [h]\n      cases nums with\n      | nil => exact absurd rfl hne\n      | cons a t => simp\n    · rw [List.mem_flatMap] at h\n      obtain ⟨j, hj, hi⟩ := h\n      rw [List.mem_map] at hi\n      obtain ⟨i, hi', hs⟩ := hi\n      rw [List.mem_range] at hj hi'\n      exact ⟨j, by omega, i, hi', hs⟩\n  · intro j hj i hi\n    apply h3\n    rw [List.mem_flatMap]\n    exact ⟨j, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩"
    }
]
_ANYINT = [
    {
        "name": "anyint_equiv",
        "statement": "∀ (x y z : PyVal), ((fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z) = true ↔ (match x, y, z with | PyVal.int a, PyVal.int b, PyVal.int c => a = b + c ∨ b = a + c ∨ c = b + a | _, _, _ => False))",
        "proof": "by\n  intro x y z\n  cases x <;> cases y <;> cases z <;> simp"
    }
]

_VOWEL_STEP = [
    {
        "name": "vowel_step",
        "statement": "∀ (w : List Char) (i : Nat) (b : Option Nat), (i ≤ w.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt w j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt w c ∧ ∀ j, j < i → c < j → ¬ goodAt w j))) → i < w.length → (i + 1 ≤ w.length ∧ (((if goodAt w i then some i else b) = none ∧ ∀ j, j < i + 1 → ¬ goodAt w j) ∨ (∃ c, (if goodAt w i then some i else b) = some c ∧ c < i + 1 ∧ goodAt w c ∧ ∀ j, j < i + 1 → c < j → ¬ goodAt w j)))",
        "proof": "by\n  intro w i b h hi\n  obtain ⟨_, hb⟩ := h\n  refine ⟨by omega, ?_⟩\n  by_cases hg : goodAt w i\n  · right\n    refine ⟨i, by rw [if_pos hg], by omega, hg, ?_⟩\n    intro j hj hij; omega\n  · rw [if_neg hg]\n    rcases hb with ⟨rfl, hn⟩ | ⟨c, rfl, hc, hgc, hmax⟩\n    · left\n      refine ⟨rfl, ?_⟩\n      intro j hj\n      by_cases hji : j < i\n      · exact hn j hji\n      · have : j = i := by omega\n        subst this; exact hg\n    · right\n      refine ⟨c, rfl, by omega, hgc, ?_⟩\n      intro j hj hcj\n      by_cases hji : j < i\n      · exact hmax j hji hcj\n      · have : j = i := by omega\n        subst this; exact hg"
    },
    {
        "name": "vowel_none",
        "statement": "∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → last = none → ((\"\" = \"\" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ (\"\" ≠ \"\" → ∃ i, i < w.length ∧ goodAt w i ∧ \"\" = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))",
        "proof": "by\n  intro w last h hn\n  rcases h with ⟨_, hnone⟩ | ⟨b, hb, _⟩\n  · exact ⟨⟨fun _ => hnone, fun _ => rfl⟩, fun h => absurd rfl h⟩\n  · rw [hn] at hb; exact absurd hb (by simp)"
    },
    {
        "name": "vowel_some",
        "statement": "∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → ¬ last = none → ((String.singleton w[last.getD 0]! = \"\" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ (String.singleton w[last.getD 0]! ≠ \"\" → ∃ i, i < w.length ∧ goodAt w i ∧ String.singleton w[last.getD 0]! = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))",
        "proof": "by\n  intro w last h hn\n  rcases h with ⟨hnone, _⟩ | ⟨b, rfl, hb, hg, hmax⟩\n  · exact absurd hnone hn\n  · have hne : String.singleton w[b]! ≠ \"\" := by\n      intro h\n      have := congrArg String.length h\n      simp at this\n    exact ⟨⟨fun h => absurd h hne, fun hn => absurd hg (hn b hb)⟩, fun _ => ⟨b, hb, hg, rfl, hmax⟩⟩"
    }
]

ORACLES_MORE = {
    "he_005_intersperse": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
             "i ≤ numbers.length ∧ acc.length = (if i = 0 then 0 else 2 * i - 1) ∧ (∀ k, k < i → acc[2 * k]! = numbers[k]!) ∧ "
             "∀ k, k + 1 < i → acc[2 * k + 1]! = delimeter",
             "i < numbers.length", "numbers.length - i", "acc",
             term("(i + 1, if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])")), _INTER),
    "he_009_rolling_max": with_lemmas(
        term("(List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)"), _ROLL),
    "he_038_decode_cyclic": with_lemmas(
        term("String.mk (encodeGroups (encodeGroups s.toList))"),
        [{"name": "encode_three", "statement": "∀ (l : List Char), encodeGroups (encodeGroups (encodeGroups l)) = l",
          "proof": "by intro l\n  induction l using encodeGroups.induct with\n  | case1 a b c rest ih => simp [encodeGroups, ih]\n"
                   "  | case2 l h => cases l with\n    | nil => simp [encodeGroups]\n    | cons a t => cases t with\n      | nil => simp [encodeGroups]\n"
                   "      | cons b t2 => cases t2 with\n        | nil => simp [encodeGroups]\n        | cons c rest => exact absurd rfl (h a b c rest)"}]),

    "he_132_is_nested": term(
        "decide (∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧ isBalancedSq ((string.toList.drop i).take len) ∧ "
        "∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k))"),
    "he_116_sort_array": with_lemmas(
        term("arr.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))"), _SORT116),
    "he_088_sort_array": with_lemmas(
        cases("array ≠ [] ∧ (array.head! + array.getLast!) % 2 = 0",
              term("array.mergeSort (fun a b => decide (a ≥ b))"), term("array.mergeSort (fun a b => decide (a ≤ b))")),
        _SORT_NAT_ASC + _SORT_NAT_DESC),
    "he_092_any_int": with_lemmas(term(
        "(fun (p : PyVal × PyVal × PyVal) => match p with | (PyVal.int a, PyVal.int b, PyVal.int c) => "
        "decide (a = b + c ∨ b = a + c ∨ c = b + a) | _ => false) (x, y, z)"), _ANYINT),
    "he_130_tri": loop(
        [["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
        "i ≤ n + 1 ∧ acc.length = i ∧ (0 < i → acc[0]! = 1) ∧ (1 < i → acc[1]! = 3) ∧ "
        "∀ k, k < i → 2 ≤ k → acc[k]! = (if k % 2 = 0 then 1 + k / 2 else acc[k - 1]! + acc[k - 2]! + (1 + (k + 1) / 2))",
        "i < n + 1", "n + 1 - i", "acc",
        term("(i + 1, acc ++ [if i = 0 then 1 else if i = 1 then 3 else if i % 2 = 0 then 1 + i / 2 else "
             "acc[i - 1]! + acc[i - 2]! + (1 + (i + 1) / 2)])")),
    "he_114_min_sub_array_sum": with_lemmas(
        term("List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))"),
        _MINSUB),

    "he_118_get_closest_vowel": with_lemmas(
        bind("last", "Option Nat",
             "(last = none ∧ ∀ i, i < word.toList.length → ¬ goodAt word.toList i) ∨ (∃ b, last = some b ∧ b < word.toList.length ∧ goodAt word.toList b ∧ ∀ j, j < word.toList.length → b < j → ¬ goodAt word.toList j)",
             loop([["i", "Nat"], ["b", "Option Nat"]], ["0", "none"],
                  "i ≤ word.toList.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt word.toList j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt word.toList c ∧ ∀ j, j < i → c < j → ¬ goodAt word.toList j))",
                  "i < word.toList.length", "word.toList.length - i", "b",
                  term("(i + 1, if goodAt word.toList i then some i else b)")),
             cases("last = none", term('""'), term("String.singleton word.toList[last.getD 0]!"))),
        _VOWEL_STEP),
}
