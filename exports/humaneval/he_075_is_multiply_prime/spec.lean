import Mathlib

@[reducible, simp]
def isMultiplyPrime_precond (a : Nat) : Prop :=
  a < 100

@[reducible, simp]
def isMultiplyPrime_postcond (a : Nat) (result: Bool) (h_precond : isMultiplyPrime_precond (a)) :=
  result = true ↔ ∃ p, p < a + 1 ∧ ∃ q, q < a + 1 ∧ ∃ r, r < a + 1 ∧ p * q * r = a ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r
