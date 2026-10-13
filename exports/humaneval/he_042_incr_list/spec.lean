import Mathlib

@[reducible, simp]
def incrList_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def incrList_postcond (l : List Int) (result: List Int) (h_precond : incrList_precond (l)) :=
  result.length = l.length ∧ ∀ i, i < l.length → result[i]! = l[i]! + 1
