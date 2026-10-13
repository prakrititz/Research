import Mathlib

@[reducible, simp]
def triplesSumToZero_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def triplesSumToZero_postcond (l : List Int) (result: Bool) (h_precond : triplesSumToZero_precond (l)) :=
  result = true ↔ ∃ k, k < l.length ∧ ∃ j, j < k ∧ ∃ i, i < j ∧ l[i]! + l[j]! + l[k]! = 0
