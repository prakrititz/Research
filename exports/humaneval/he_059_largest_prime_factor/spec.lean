import Mathlib

@[reducible, simp]
def largestPrimeFactor_precond (n : Nat) : Prop :=
  n > 1 ∧ ¬ Nat.Prime n

@[reducible, simp]
def largestPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : largestPrimeFactor_precond (n)) :=
  Nat.Prime result ∧ result ∣ n ∧ ∀ q, q < n + 1 → Nat.Prime q → q ∣ n → q ≤ result
