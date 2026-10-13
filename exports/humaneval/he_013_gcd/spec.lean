import Mathlib

@[reducible, simp]
def greatestCommonDivisor_precond (a : Nat) (b : Nat) : Prop :=
  a > 0 ∧ b > 0

@[reducible, simp]
def greatestCommonDivisor_postcond (a : Nat) (b : Nat) (result: Nat) (h_precond : greatestCommonDivisor_precond (a) (b)) :=
  result > 0 ∧ a % result = 0 ∧ b % result = 0 ∧ ∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ result
