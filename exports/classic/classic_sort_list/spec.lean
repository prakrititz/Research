import Mathlib

@[reducible, simp]
def sortList_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def sortList_postcond (l : List Int) (result: List Int) (h_precond : sortList_precond (l)) :=
  (∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧ result.isPerm l
