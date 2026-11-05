namespace Refine

theorem foldl_max_mem_of_mem {α : Type} [LinearOrder α] (l : List α) (m : α) (h : m ∈ l) : List.foldl max m l ∈ l := by
  rcases (foldl_max_facts l m).1 with h1 | h1
  · rw [h1]; exact h
  · exact h1

theorem le_foldl_max {α : Type} [LinearOrder α] (l : List α) (m x : α) (h : x ∈ l) : x ≤ List.foldl max m l :=
  (foldl_max_facts l m).2.2 x h

theorem start_le_foldl_max {α : Type} [LinearOrder α] (l : List α) (m : α) : m ≤ List.foldl max m l :=
  (foldl_max_facts l m).2.1

theorem getElem_bang_zero_mem_take {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : l ≠ []) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => contradiction
  | cons x xs => simp

theorem getElem_bang_zero_mem_take' {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : 0 < l.length) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

end Refine

-- the shape left open in he_009 (rolling maximum), with the precondition `numbers ≠ []`
example (numbers : List Int) (hne : numbers ≠ []) : ∀ i < numbers.length,
    ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! := by
  intros i hi
  simp only [Refine.getElem_bang_map_range _ _ _ hi]
  exact ⟨Refine.foldl_max_mem_of_mem _ _ (Refine.getElem_bang_zero_mem_take _ _ hne), fun x hx => Refine.le_foldl_max _ _ _ hx⟩

-- the same goal, closed by the cascade's new step (intros; simp_all [...]; grind [...]) if the lemmas are in the sets
example (numbers : List Int) (hne : numbers ≠ []) : ∀ i < numbers.length,
    ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! := by
  intros i hi
  simp_all [Refine.getElem_bang_map_range, Refine.le_foldl_max]
  grind [Refine.foldl_max_mem_of_mem, Refine.getElem_bang_zero_mem_take, Refine.le_foldl_max]
