import Mathlib

@[reducible, simp]
def reverseList_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def reverseList_postcond (l : List Int) (result: List Int) (h_precond : reverseList_precond (l)) :=
  result.length = l.length ∧ ∀ i, i < l.length → result[i]! = l[l.length - 1 - i]!
