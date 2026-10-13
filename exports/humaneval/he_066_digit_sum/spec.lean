import Mathlib

@[reducible, simp]
def digitSum_precond (s : String) : Prop :=
  True

@[reducible, simp]
def digitSum_postcond (s : String) (result: Nat) (h_precond : digitSum_precond (s)) :=
  result = ((s.toList.filter Char.isUpper).map Char.toNat).sum
