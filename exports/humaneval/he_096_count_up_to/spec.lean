import Mathlib

@[reducible, simp]
def countUpTo_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def countUpTo_postcond (n : Nat) (result: List Nat) (h_precond : countUpTo_precond (n)) :=
  (∀ p ∈ result, p < n ∧ Nat.Prime p) ∧ (∀ p, p < n → Nat.Prime p → p ∈ result) ∧ ∀ i, i < result.length - 1 → result[i]! < result[i + 1]!
