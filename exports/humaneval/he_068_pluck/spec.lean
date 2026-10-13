import Mathlib

@[reducible, simp]
def pluck_precond (arr : List Nat) : Prop :=
  True

@[reducible, simp]
def pluck_postcond (arr : List Nat) (result: List Nat) (h_precond : pluck_precond (arr)) :=
  (result = [] ↔ ∀ x ∈ arr, x % 2 = 1) ∧
    (result ≠ [] → result.length = 2 ∧ result[1]! < arr.length ∧ arr[result[1]!]! = result[0]! ∧ result[0]! % 2 = 0 ∧
      (∀ x ∈ arr, x % 2 = 0 → result[0]! ≤ x) ∧ ∀ j, j < result[1]! → arr[j]! ≠ result[0]!)
