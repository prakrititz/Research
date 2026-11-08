/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (x : Nat) (base : Nat) (h_precond : changeBase_precond x base) :
    changeBase_postcond x base (String.mk (Nat.toDigits base x)) h_precond := by
  sorry
