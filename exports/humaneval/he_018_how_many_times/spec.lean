import Mathlib

@[reducible, simp]
def howManyTimes_precond (string : String) (substring : String) : Prop :=
  True

@[reducible, simp]
def howManyTimes_postcond (string : String) (substring : String) (result: Nat) (h_precond : howManyTimes_precond (string) (substring)) :=
  result = ((List.range string.length).filter (fun i => substring.toList.isPrefixOf (string.toList.drop i))).length
