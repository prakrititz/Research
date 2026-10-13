import Mathlib

@[reducible, simp]
def moveOneBall_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def moveOneBall_postcond (arr : List Int) (result: Bool) (h_precond : moveOneBall_precond (arr)) :=
  result = true ↔ ∃ i, i < arr.length + 1 ∧ arr.drop i ++ arr.take i = arr.mergeSort (fun a b => a ≤ b)
