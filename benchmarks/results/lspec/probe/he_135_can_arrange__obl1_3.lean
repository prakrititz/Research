/- exit: on exit the invariant and the negated guard imply the postcondition
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (arr : List Int) (i : Nat) (h_precond : canArrange_precond arr) (h1i : ((i ≤ (arr.length - 1)) ∧ (∀ m, (m < arr.length) → ((i < m) → (arr[m - 1]! ≤ arr[m]!))))) (h1g : ¬ ((1 ≤ i) ∧ (arr[i - 1]! ≤ arr[i]!))) :
    canArrange_postcond arr (if i = 0 then (-1 : Int) else (i : Int)) h_precond := by
  sorry
