namespace Refine

theorem mergeSort_isPerm {α : Type} [BEq α] [LawfulBEq α] (l : List α) (f : α → α → Bool) :
    (l.mergeSort f).isPerm l = true := by
  rw [List.isPerm_iff]
  exact List.mergeSort_perm l f

theorem isPerm_mergeSort {α : Type} [BEq α] [LawfulBEq α] (l : List α) (f : α → α → Bool) :
    l.isPerm (l.mergeSort f) = true := by
  rw [List.isPerm_iff]
  exact (List.mergeSort_perm l f).symm

theorem mergeSort_sorted_by {α : Type} [Inhabited α] (l : List α) (f : α → α → Bool)
    (trans : ∀ a b c, f a b = true → f b c = true → f a c = true) (total : ∀ a b, (f a b || f b a) = true) :
    ∀ i, i < (l.mergeSort f).length - 1 → f (l.mergeSort f)[i]! (l.mergeSort f)[i + 1]! = true := by
  intro i hi
  have hs := List.pairwise_mergeSort trans total l
  have h1 : i < (l.mergeSort f).length := by omega
  have h2 : i + 1 < (l.mergeSort f).length := by omega
  rw [getElem!_pos _ i h1, getElem!_pos _ (i + 1) h2]
  exact List.pairwise_iff_getElem.mp hs i (i + 1) h1 h2 (by omega)

theorem mergeSort_le_int (l : List Int) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_ge_int (l : List Int) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≥ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (l.mergeSort (fun a b => decide (a ≥ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_le_nat (l : List Nat) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_key_le {α : Type} [Inhabited α] (key : α → Int) (l : List α) :
    ∀ i, i < (l.mergeSort (fun a b => decide (key a ≤ key b))).length - 1 →
      key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i]! ≤ key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_key_le_nat {α : Type} [Inhabited α] (key : α → Nat) (l : List α) :
    ∀ i, i < (l.mergeSort (fun a b => decide (key a ≤ key b))).length - 1 →
      key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i]! ≤ key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_length' {α : Type} (l : List α) (f : α → α → Bool) : (l.mergeSort f).length = l.length :=
  List.length_mergeSort l

theorem mem_mergeSort' {α : Type} (l : List α) (f : α → α → Bool) (x : α) : x ∈ l.mergeSort f ↔ x ∈ l :=
  (List.mergeSort_perm l f).mem_iff

end Refine

example (arr : List Int) : (arr.mergeSort fun a b => decide (a ≥ b)).isPerm arr = true := Refine.mergeSort_isPerm _ _
example (l : List Int) : ∀ i < (l.mergeSort fun a b => decide (a ≤ b)).length - 1,
    (l.mergeSort fun a b => decide (a ≤ b))[i]! ≤ (l.mergeSort fun a b => decide (a ≤ b))[i + 1]! := Refine.mergeSort_le_int l
