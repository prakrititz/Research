/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (N : Nat) (h_precond : solve84_precond N) :
    solve84_postcond N (String.mk (Nat.toDigits 2 ((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum)) h_precond := by
  sorry
