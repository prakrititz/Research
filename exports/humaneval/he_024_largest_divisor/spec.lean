import Mathlib

@[reducible, simp]
def largestDivisor_precond (n : Nat) : Prop :=
  n > 1

@[reducible, simp]
def largestDivisor_postcond (n : Nat) (result: Nat) (h_precond : largestDivisor_precond (n)) :=
  result > 0 ∧ result < n ∧ n % result = 0 ∧ ∀ d, d < n → result < d → n % d ≠ 0
