/- exit: on exit the invariant and the negated guard imply the postcondition
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (n : Nat) (x : Nat) (c : Nat) (h_precond : nthUglyNumber_precond n) (h1i : ((x ≤ (2 ^ (n - 1))) ∧ ((c = ((List.range x).filter (fun i => isUgly i)).length) ∧ (c < n)))) (h1g : ¬ ((x < (2 ^ (n - 1))) ∧ (¬ (((isUgly x) = true) ∧ ((c + 1) = n))))) :
    nthUglyNumber_postcond n (x) h_precond := by
  sorry
