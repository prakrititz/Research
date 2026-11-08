/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (s : String) (h_precond : decodeCyclic_precond s) :
    decodeCyclic_postcond s (String.mk (encodeGroups (encodeGroups s.toList))) h_precond := by
  sorry
