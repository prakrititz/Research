/- exit: on exit the invariant and the negated guard imply the postcondition
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
n q : ℕ
h_precond : largestPrimeFactor_precond n
h1i : 1 ≤ q ∧ q ≤ n ∧ ∀ r < n + 1, q < r → Nat.Prime r → r ∣ n → False
h1g : ¬(1 < q ∧ ¬(Nat.Prime q ∧ n % q = 0))
⊢ Nat.Prime q

case right.left
n q : ℕ
h_precond : largestPrimeFactor_precond n
h1i : 1 ≤ q ∧ q ≤ n ∧ ∀ r < n + 1, q < r → Nat.Prime r → r ∣ n → False
h1g : ¬(1 < q ∧ ¬(Nat.Prime q ∧ n % q = 0))
⊢ q ∣ n
-/
theorem probe (n : Nat) (q : Nat) (h_precond : largestPrimeFactor_precond n) (h1i : ((1 ≤ q) ∧ ((q ≤ n) ∧ (∀ r, (r < (n + 1)) → ((q < r) → ((Nat.Prime r) → ((r ∣ n) → False))))))) (h1g : ¬ ((1 < q) ∧ (¬ ((Nat.Prime q) ∧ ((n % q) = 0))))) :
    largestPrimeFactor_postcond n (q) h_precond := by
  sorry
