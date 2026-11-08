/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (n : Nat) (m : Nat) (h_precond : roundedAvg_precond n m) (h1 : ¬ (n > m)) :
    roundedAvg_postcond n m (some (String.mk (['0', 'b'] ++ (Nat.toDigits 2 (roundedHalfEven (n + m)))))) h_precond := by
  sorry
