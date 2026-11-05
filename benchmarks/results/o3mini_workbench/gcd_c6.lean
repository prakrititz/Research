-- chunk 6
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.getElem_bang_zero_mem_take_of_lt, Refine.getElem_bang_cons, Refine.getElem_bang_nil, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mergeSort_le_int, Refine.mergeSort_ge_int, Refine.mergeSort_le_nat, Refine.mergeSort_key_le, Refine.mergeSort_key_le_nat, Refine.le_gcd_of_mod_left]

