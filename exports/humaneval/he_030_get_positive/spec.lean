import Mathlib

@[reducible, simp]
def getPositive_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def getPositive_postcond (l : List Int) (result: List Int) (h_precond : getPositive_precond (l)) :=
  result = l.filter (fun x => x > 0)
