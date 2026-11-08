/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (decimal : Nat) (h_precond : decimalToBinary_precond decimal) :
    decimalToBinary_postcond decimal (String.mk ((['d', 'b'] ++ (Nat.toDigits 2 decimal)) ++ ['d', 'b'])) h_precond := by
  sorry
