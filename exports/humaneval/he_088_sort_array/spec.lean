import Mathlib

@[reducible, simp]
def sortArray88_precond (array : List Nat) : Prop :=
  True

@[reducible, simp]
def sortArray88_postcond (array : List Nat) (result: List Nat) (h_precond : sortArray88_precond (array)) :=
  result.isPerm array ∧ (array ≠ [] → ((array.head! + array.getLast!) % 2 = 1 → ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧
      ((array.head! + array.getLast!) % 2 = 0 → ∀ i, i < result.length - 1 → result[i + 1]! ≤ result[i]!))
