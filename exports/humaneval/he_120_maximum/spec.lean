import Mathlib

@[reducible, simp]
def maximum_precond (arr : List Int) (k : Nat) : Prop :=
  k ≤ arr.length

@[reducible, simp]
def maximum_postcond (arr : List Int) (k : Nat) (result: List Int) (h_precond : maximum_precond (arr) (k)) :=
  result.isPerm ((arr.mergeSort (fun a b => a ≥ b)).take k) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
