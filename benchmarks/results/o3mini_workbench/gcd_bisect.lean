-- chunk 0
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.mem_iff_idx, Refine.le_gcd_of_mod_left]

-- chunk 1
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.toList_getElem_bang, Refine.forall_mem_toList_iff_idx, Refine.le_gcd_of_mod_left]

-- chunk 2
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, Refine.forall_mem_drop_iff, Refine.exists_mem_drop_iff, Refine.forall_mem_take_iff, Refine.arr_all_take_iff, Refine.arr_all_drop_iff, Refine.sorted_arr_le, Refine.foldl_max_facts, Refine.le_gcd_of_mod_left]

-- chunk 3
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.maxlist_nat, Refine.maxlist_int, Refine.allsub_nil_mem, Refine.allsub_nil_mem_arr, Refine.allsub_rev_nil_mem, Refine.longest_facts, Refine.longest_spec, Refine.maxlist_int_any, Refine.maxlen_spec, Refine.filter_pair_le, Refine.le_gcd_of_mod_left]

-- chunk 4
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.count_pair_le, Refine.find_some_of_any, Refine.find_majority, Refine.ts_inner_init, Refine.ts_outer_init, Refine.ts_inner_step, Refine.ts_inner_exit, Refine.ts_outer_step, Refine.ts_lex_all, Refine.ts_pairwise_none, Refine.le_gcd_of_mod_left]

-- chunk 5
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.getElem_bang_map_range, Refine.getElem_bang_append, Refine.pairwise_le_nodup_lt, Refine.dedup_mergeSort_strict, Refine.mem_dedup_mergeSort, Refine.foldl_max_mem_of_mem, Refine.le_foldl_max, Refine.start_le_foldl_max, Refine.getElem_bang_zero_mem_take, Refine.getElem_bang_zero_mem_take', Refine.le_gcd_of_mod_left]

-- chunk 6
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.getElem_bang_zero_mem_take_of_lt, Refine.getElem_bang_cons, Refine.getElem_bang_nil, Refine.mergeSort_isPerm, Refine.isPerm_mergeSort, Refine.mergeSort_le_int, Refine.mergeSort_ge_int, Refine.mergeSort_le_nat, Refine.mergeSort_key_le, Refine.mergeSort_key_le_nat, Refine.le_gcd_of_mod_left]

-- chunk 7
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.mergeSort_length', Refine.mem_mergeSort', Refine.mod_gcd_left, Refine.mod_gcd_right, Refine.mod_eq_zero_of_dvd', Refine.dvd_of_mod_eq_zero', Refine.le_of_dvd_pos, Refine.mergeSort_ge_nat, Refine.foldl_min_facts, Refine.foldl_min_mem_of_mem, Refine.le_gcd_of_mod_left]

-- chunk 8
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.foldl_min_le, Refine.foldl_min_le_start, Refine.le_gcd_of_mod_left]
