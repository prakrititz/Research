-- two counters in one fold: `if p i then (if q i then first + 1 else second + 1)` counts the filters (he_107: even and odd
-- palindromes in one pass, against the specification's two `filter ... |>.length`)
theorem foldl_pair_count {α : Type} (l : List α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] (a b : Nat) :
    l.foldl (fun acc i => if p i then if q i then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1) else acc) (a, b) =
      (a + (l.filter fun i => decide (p i ∧ q i)).length, b + (l.filter fun i => decide (p i ∧ ¬ q i)).length) := by
  induction l generalizing a b with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq, ih] <;> omega
theorem foldl_pair_count_fst {α : Type} (l : List α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] (r : α → Bool)
    (hr : ∀ x, r x = true ↔ p x ∧ q x) :
    (l.foldl (fun acc i => if p i then if q i then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1) else acc) (0, 0)).1 =
      (l.filter r).length := by
  simp only [foldl_pair_count, Nat.zero_add]
  congr 1; apply List.filter_congr; intro x _
  exact Bool.eq_iff_iff.mpr (by simp [hr x])
theorem foldl_pair_count_snd {α : Type} (l : List α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] (r : α → Bool)
    (hr : ∀ x, r x = true ↔ p x ∧ ¬ q x) :
    (l.foldl (fun acc i => if p i then if q i then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1) else acc) (0, 0)).2 =
      (l.filter r).length := by
  simp only [foldl_pair_count, Nat.zero_add]
  congr 1; apply List.filter_congr; intro x _
  exact Bool.eq_iff_iff.mpr (by simp [hr x])

-- rounding half away from zero, for a non-negative rational: `⌊q + 1/2⌋` (he_099)
theorem floor_add_half_spec (q : ℚ) (h : q ≥ 0) :
    |q - (⌊q + 1 / 2⌋ : ℚ)| < 1 / 2 ∨ (|q - (⌊q + 1 / 2⌋ : ℚ)| = 1 / 2 ∧ |q| < |(⌊q + 1 / 2⌋ : ℚ)|) := by
  have h1 := Int.floor_le (q + 1 / 2)
  have h2 := Int.lt_floor_add_one (q + 1 / 2)
  rcases lt_or_eq_of_le h1 with h3 | h3
  · left; rw [abs_lt]; constructor <;> linarith
  · right
    have hr : (0 : ℚ) < (⌊q + 1 / 2⌋ : ℚ) := by linarith
    refine ⟨?_, ?_⟩
    · rw [h3]; norm_num [abs_of_neg]
    · rw [abs_of_nonneg h, abs_of_pos hr]; linarith

-- a list of characters as a string and back (he_027: `(l.map f).asString`)
theorem asString_toList' (l : List Char) : l.asString.toList = l := by simp [List.asString]
theorem asString_length' (l : List Char) : l.asString.length = l.length := by simp [List.asString]
theorem append_mk_toList (s : String) (l : List Char) : (s ++ String.mk l).toList = s.toList ++ l := by
  simp [String.toList_append, string_toList_mk]
theorem append_mk_length (s : String) (l : List Char) : (s ++ String.mk l).length = s.length + l.length := by
  simp [String.length_append, string_length_mk]
