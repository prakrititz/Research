-- chunk 2
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.forall_mem_drop_iff, Refine.exists_mem_drop_iff, Refine.forall_mem_take_iff, Refine.arr_all_take_iff, Refine.arr_all_drop_iff, Refine.sorted_arr_le, Refine.foldl_max_facts, Refine.le_gcd_of_mod_left]

