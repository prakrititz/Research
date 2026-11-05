example (numbers : List Int) (i : Nat) (hi : i < numbers.length) :
    List.foldl max numbers[0]! (List.take (i + 1) numbers) ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ List.foldl max numbers[0]! (List.take (i + 1) numbers) := by
  grind [Refine.foldl_max_mem_of_mem, Refine.getElem_bang_zero_mem_take', Refine.le_foldl_max]

example (numbers : List Int) (i : Nat) (hi : i < numbers.length) :
    List.foldl max numbers[0]! (List.take (i + 1) numbers) ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ List.foldl max numbers[0]! (List.take (i + 1) numbers) := by
  refine ⟨?_, ?_⟩
  · apply Refine.foldl_max_mem_of_mem; all_goals first | assumption | (simp_all; done) | omega | (apply Refine.getElem_bang_zero_mem_take'; omega)
  · intro x hx; apply Refine.le_foldl_max; assumption
