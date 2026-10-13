import Mathlib

@[reducible, simp]
def pairsSumToZero_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def pairsSumToZero_postcond (l : List Int) (result: Bool) (h_precond : pairsSumToZero_precond (l)) :=
  result = true ↔ ∃ j, j < l.length ∧ ∃ i, i < j ∧ l[i]! + l[j]! = 0
