/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (value : String) (h_precond : closestInteger_precond value) :
    closestInteger_postcond value (if (parseDec value) ≥ 0 then ⌊(parseDec value) + (1 / 2)⌋ else -⌊(-(parseDec value)) + (1 / 2)⌋) h_precond := by
  sorry
