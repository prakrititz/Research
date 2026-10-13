import Mathlib

@[reducible, simp]
def factorize_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def factorize_postcond (n : Nat) (result: List Nat) (h_precond : factorize_precond (n)) :=
  result.prod = n ∧ (∀ p ∈ result, Nat.Prime p) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
