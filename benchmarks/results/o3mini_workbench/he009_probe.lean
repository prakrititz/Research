example (numbers : List Int) (h_precond : rollingMax_precond numbers) : ∀ i < numbers.length,
    ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! ∈ List.take (i + 1) numbers ∧
    ∀ x ∈ List.take (i + 1) numbers, x ≤ ((List.range numbers.length).map (fun i => List.foldl max numbers[0]! (List.take (i + 1) numbers)))[i]! := by
  intros i hi
  simp_all [Refine.getElem_bang_map_range, -List.getElem!_eq_getElem?_getD]
  trace_state
  sorry
