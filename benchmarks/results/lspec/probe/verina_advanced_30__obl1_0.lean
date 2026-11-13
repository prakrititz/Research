/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (nums : List Int) (h_precond : longestIncreasingStreak_precond nums) :
    longestIncreasingStreak_postcond nums (((List.range (nums.length + 1)).flatMap (fun s => (List.range (nums.length + 1)).filter (fun L => decide (((s + L) ≤ nums.length) ∧ (((List.range L).all (fun i => decide (((i + 1) < L) → (nums[s + i]! < nums[(s + i) + 1]!)))) = true))))).foldl max 0) h_precond := by
  sorry
