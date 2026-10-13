import Mathlib

@[reducible, simp]
def generateIntegers_precond (a : Nat) (b : Nat) : Prop :=
  True

@[reducible, simp]
def generateIntegers_postcond (a : Nat) (b : Nat) (result: List Nat) (h_precond : generateIntegers_precond (a) (b)) :=
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ d ∈ result, d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b ∧ d < 10) ∧
    ∀ d, d < 10 → d % 2 = 0 → min a b ≤ d → d ≤ max a b → d ∈ result
