-- chunk 3
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.maxlist_nat, Refine.maxlist_int, Refine.allsub_nil_mem, Refine.allsub_nil_mem_arr, Refine.allsub_rev_nil_mem, Refine.longest_facts, Refine.longest_spec, Refine.maxlist_int_any, Refine.maxlen_spec, Refine.filter_pair_le, Refine.le_gcd_of_mod_left]

