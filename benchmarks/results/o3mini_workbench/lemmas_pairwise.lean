namespace Refine
theorem pairwise_mergeSort_le_int (l : List Int) : List.Pairwise (fun a b => a ≤ b) (l.mergeSort (fun a b => decide (a ≤ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_le_nat (l : List Nat) : List.Pairwise (fun a b => a ≤ b) (l.mergeSort (fun a b => decide (a ≤ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_ge_int (l : List Int) : List.Pairwise (fun a b => a ≥ b) (l.mergeSort (fun a b => decide (a ≥ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_ge_nat (l : List Nat) : List.Pairwise (fun a b => a ≥ b) (l.mergeSort (fun a b => decide (a ≥ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_key_le {α : Type} (key : α → Int) (l : List α) :
    List.Pairwise (fun a b => key a ≤ key b) (l.mergeSort (fun a b => decide (key a ≤ key b))) := by
  have := List.pairwise_mergeSort (le := fun a b : α => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
end Refine
example (xs : List Int) : List.Pairwise (fun x1 x2 => x1 ≤ x2) (xs.mergeSort fun a b => decide (a ≤ b)) := by
  solve_by_elim [Refine.pairwise_mergeSort_le_int]
