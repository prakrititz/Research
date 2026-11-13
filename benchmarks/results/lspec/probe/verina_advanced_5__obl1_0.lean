/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond l1 l2) :
    addTwoNumbers_postcond l1 l2 (if ((listToNat l1) + (listToNat l2)) = 0 then [0] else Nat.digits 10 ((listToNat l1) + (listToNat l2))) h_precond := by
  sorry
