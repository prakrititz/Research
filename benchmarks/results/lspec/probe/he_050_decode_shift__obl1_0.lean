/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (s : String) (h_precond : decodeShift_precond s) :
    decodeShift_postcond s (String.mk (s.toList.map (fun c => Char.ofNat ((((c.toNat - 97) + 21) % 26) + 97)))) h_precond := by
  sorry
