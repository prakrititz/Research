r"""Hand-written derivations for Verina tasks, batch X (advanced: rain water, longest increasing run)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

# --- 62 rain: the postcondition's own recursion, with the proof that the sum of non-negative terms is non-negative ----------------
_E62 = ("if heights.length < 3 then 0 else rain_postcond.sum_water heights (fun i => max 0 "
        "(min (rain_postcond.ml heights i 0 0) (rain_postcond.mr heights i 0) - heights[i]!)) 0 0")
_NN62 = {
    "name": "nonneg_sw",
    "statement": "∀ (heights : List Int) (w : Nat → Int), (∀ i, 0 ≤ w i) → ∀ (n i : Nat) (acc : Int), heights.length - i ≤ n → 0 ≤ acc → "
                 "0 ≤ rain_postcond.sum_water heights w i acc",
    "proof": "by intro heights w hw n\n  induction n with\n  | zero =>\n    intro i acc hn hacc\n    rw [rain_postcond.sum_water]\n"
             "    split_ifs with h\n    · exact hacc\n    · omega\n"
             "  | succ n ih =>\n    intro i acc hn hacc\n    rw [rain_postcond.sum_water]\n    split_ifs with h\n    · exact hacc\n"
             "    · exact ih (i + 1) _ (by omega) (by have := hw i; omega)"}
_L62 = {
    "name": "rain62",
    "statement": "∀ (heights : List Int) (h : rain_precond heights), rain_postcond heights (" + _E62 + ") h",
    "proof": "by intro heights h\n  unfold rain_postcond\n  by_cases hl : heights.length < 3\n"
             "  · rw [if_pos hl]; refine ⟨le_refl _, ?_⟩; rw [if_pos hl]\n"
             "  · rw [if_neg hl]\n"
             "    refine ⟨nonneg_sw heights _ (fun i => le_max_left _ _) heights.length 0 0 (by omega) (le_refl _), ?_⟩\n"
             "    rw [if_neg hl]"}

# --- 30 longestIncreasingStreak: the longest window that is strictly increasing -------------------------------------------------
def _inc(s, L):
    return f"((List.range {L}).all (fun i => decide (i + 1 < {L} → nums[{s} + i]! < nums[{s} + i + 1]!)) = true)"


_D30 = ("(List.range (nums.length + 1)).flatMap (fun s => (List.range (nums.length + 1)).filter (fun L => "
        "decide (s + L ≤ nums.length ∧ (List.range L).all (fun i => decide (i + 1 < L → nums[s + i]! < nums[s + i + 1]!)) = true)))")
_E30 = "(" + _D30 + ").foldl max 0"
_L30 = {
    "name": "streak30",
    "statement": "∀ (nums : List Int) (h : longestIncreasingStreak_precond nums), longestIncreasingStreak_postcond nums (" + _E30 + ") h",
    "proof": "by intro nums h\n  unfold longestIncreasingStreak_postcond\n"
             f"  generalize hD : {_D30} = D\n"
             "  have hmemD : ∀ d, d ∈ D ↔ ∃ s, s < nums.length + 1 ∧ d < nums.length + 1 ∧ s + d ≤ nums.length ∧ "
             "(∀ i, i + 1 < d → nums[s + i]! < nums[s + i + 1]!) := by\n"
             "    intro d; rw [← hD]\n"
             "    simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq, List.all_eq_true]\n"
             "    constructor\n    · rintro ⟨s, hs, hd, hc, hall⟩; exact ⟨s, hs, hd, hc, fun i hi => hall i (by omega) hi⟩\n"
             "    · rintro ⟨s, hs, hd, hc, hall⟩; exact ⟨s, hs, hd, hc, fun i hi' hi => hall i hi⟩\n"
             "  obtain ⟨h1, h2, h3⟩ := Refine.foldl_max_facts D 0\n"
             "  generalize D.foldl max 0 = M at h1 h2 h3\n"
             "  have hbound : ∀ s d, s + d ≤ nums.length → (∀ i, i + 1 < d → nums[s + i]! < nums[s + i + 1]!) → d ≤ M := by\n"
             "    intro s d hsd hinc\n    exact h3 d ((hmemD d).mpr ⟨s, by omega, by omega, hsd, hinc⟩)\n"
             "  have hmax : M > 0 → ∃ s, s + M ≤ nums.length ∧ (∀ i, i + 1 < M → nums[s + i]! < nums[s + i + 1]!) := by\n"
             "    intro hM\n    have hmem : M ∈ D := by\n      rcases h1 with h | h\n      · omega\n      · exact h\n"
             "    obtain ⟨s, _, _, hc, hinc⟩ := (hmemD M).mp hmem\n    exact ⟨s, hc, hinc⟩\n"
             "  refine ⟨?_, ?_, ?_⟩\n"
             "  · intro hnil\n    have : nums.length = 0 := by rw [hnil]; rfl\n"
             "    have := hbound 0 M (by omega)\n    by_contra hM\n    obtain ⟨s, hs, _⟩ := hmax (by omega)\n    omega\n"
             "  · intro hM\n    obtain ⟨s, hs, hinc⟩ := hmax hM\n"
             "    rw [List.any_eq_true]\n    refine ⟨s, List.mem_range.mpr (by omega), ?_⟩\n"
             "    simp only [decide_eq_true_eq, List.all_eq_true, List.mem_range]\n"
             "    refine ⟨hs, ?_, ?_, ?_⟩\n"
             "    · intro i hi\n      exact hinc i (by omega)\n"
             "    · by_cases hs0 : s = 0\n      · exact Or.inl hs0\n      · right\n        by_contra hlt\n        have hlt' : nums[s - 1]! < nums[s]! := by omega\n"
             "        have := hbound (s - 1) (M + 1) (by omega) (by\n          intro i hi\n          rcases Nat.eq_zero_or_pos i with rfl | hpos\n"
             "          · simp only [Nat.add_zero]\n            rw [show s - 1 + 1 = s from by omega]; exact hlt'\n          · have := hinc (i - 1) (by omega)\n            have e1 : s - 1 + i = s + (i - 1) := by omega\n"
             "            have e2 : s - 1 + i + 1 = s + (i - 1) + 1 := by omega\n            rw [e1]; exact this)\n        omega\n"
             "    · by_cases hse : s + M = nums.length\n      · exact Or.inl hse\n      · right\n        by_contra hlt\n"
             "        have hlt' : nums[s + M - 1]! < nums[s + M]! := by omega\n"
             "        have := hbound s (M + 1) (by omega) (by\n          intro i hi\n          by_cases hiM : i + 1 < M\n"
             "          · exact hinc i hiM\n          · have : i = M - 1 := by omega\n            subst this\n"
             "            have e : s + (M - 1) + 1 = s + M := by omega\n            rw [e, show s + (M - 1) = s + M - 1 from by omega]; exact hlt')\n        omega\n"
             "  · rw [List.all_eq_true]; intro start hstart\n    have hst := List.mem_range.mp hstart\n"
             "    rw [List.any_eq_true]\n    by_contra hno\n"
             "    have hinc : ∀ i, i + 1 < M + 1 → nums[start + i]! < nums[start + i + 1]! := by\n"
             "      intro i hi\n      by_contra hge\n      apply hno\n      refine ⟨i, List.mem_range.mpr (by omega), ?_⟩\n"
             "      simp only [Bool.or_eq_true, decide_eq_true_eq]\n      right\n      omega\n"
             "    have := hbound start (M + 1) (by omega) hinc\n    omega"}

ORACLES_MORE = {
    "verina_advanced_62": with_lemmas(term("(" + _E62 + ")"), [_NN62, _L62]),
    "verina_advanced_30": with_lemmas(term("(" + _E30 + ")"), [_L30]),
}
