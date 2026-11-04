@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse
example (n : ℕ) : (List.foldl
        (fun acc i =>
          if 1 ≤ i ∧ isPal (toString i).toList then if i % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)
          else acc)
        (0, 0) (List.range (n + 1))).1 =
    (List.filter (fun i => decide (1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0)) (List.range (n + 1))).length := by
  apply Refine.foldl_pair_count_fst; intro x; grind
example (n : ℕ) : (List.foldl
        (fun acc i =>
          if 1 ≤ i ∧ isPal (toString i).toList then if i % 2 = 0 then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)
          else acc)
        (0, 0) (List.range (n + 1))).2 =
    (List.filter (fun i => decide (1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1)) (List.range (n + 1))).length := by
  apply Refine.foldl_pair_count_snd; intro x; grind

def parseDec (s : String) : ℚ := (s.length : ℚ) / 2
example (value : String) (h1 : parseDec value ≥ 0) :
    let q := parseDec value
    |q - (⌊parseDec value + 1 / 2⌋ : ℚ)| < 1 / 2 ∨ (|q - (⌊parseDec value + 1 / 2⌋ : ℚ)| = 1 / 2 ∧ |q| < |(⌊parseDec value + 1 / 2⌋ : ℚ)|) := by
  dsimp only; apply Refine.floor_add_half_spec; assumption

def flipChar (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
example (string : String) : (string.toList.map flipChar).asString.length = string.length ∧
    ∀ i, i < string.length → (string.toList.map flipChar).asString.toList[i]! = flipChar string.toList[i]! := by
  simp only [Refine.asString_toList', Refine.asString_length']
  constructor
  · simp [String.length_toList]
  · intro i hi; simp_all [getElem!_pos, String.length]
example (string acc : String) (i : ℕ) (c : Char) (hc : c = flipChar string.toList[i]!) (h1 : acc.length = i)
    (h2 : ∀ j, j < i → acc.toList[j]! = flipChar string.toList[j]!) (hg : i < string.length) :
    (acc ++ String.mk [c]).length = i + 1 ∧ ∀ j, j < i + 1 → (acc ++ String.mk [c]).toList[j]! = flipChar string.toList[j]! := by
  simp only [Refine.append_mk_toList, Refine.append_mk_length]
  refine ⟨by simp [h1], fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
  · rw [Refine.getElem_bang_append_lt _ _ _ (by simp [String.length] at h1 ⊢; omega)]; exact h2 j h
  · subst h; rw [show acc.length = acc.toList.length by simp [String.length]] at h1
    rw [← h1, Refine.getElem_bang_append_length]; simp [hc, h1]
