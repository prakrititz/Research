namespace Refine
theorem foldl_min_facts {α : Type} [LinearOrder α] (l : List α) : ∀ (m : α),
    (List.foldl min m l = m ∨ List.foldl min m l ∈ l) ∧ List.foldl min m l ≤ m ∧ ∀ x ∈ l, List.foldl min m l ≤ x := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
    intro m
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2, h3⟩ := ih (min m a)
    refine ⟨?_, le_trans h2 (min_le_left _ _), ?_⟩
    · rcases h1 with h | h
      · rcases min_choice m a with hm | hm
        · left; rw [h, hm]
        · right; left; rw [h, hm]
      · right; right; exact h
    · rintro x (rfl | hx)
      · exact le_trans h2 (min_le_right _ _)
      · exact h3 x hx
theorem foldl_min_mem_of_mem {α : Type} [LinearOrder α] (l : List α) (m : α) (h : m ∈ l) : List.foldl min m l ∈ l := by
  rcases (foldl_min_facts l m).1 with h1 | h1
  · rw [h1]; exact h
  · exact h1
theorem foldl_min_le {α : Type} [LinearOrder α] (l : List α) (m x : α) (h : x ∈ l) : List.foldl min m l ≤ x :=
  (foldl_min_facts l m).2.2 x h
theorem foldl_min_le_start {α : Type} [LinearOrder α] (l : List α) (m : α) : List.foldl min m l ≤ m :=
  (foldl_min_facts l m).2.1
end Refine
