-- chunk 4
example (a b : Nat) (h_precond : greatestCommonDivisor_precond a b) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (try unfold greatestCommonDivisor_precond at *); (try casesm* _ ∧ _); solve_by_elim (maxDepth := 6) [Refine.count_pair_le, Refine.find_some_of_any, Refine.find_majority, Refine.ts_inner_init, Refine.ts_outer_init, Refine.ts_inner_step, Refine.ts_inner_exit, Refine.ts_outer_step, Refine.ts_lex_all, Refine.ts_pairwise_none, Refine.le_gcd_of_mod_left]

