import Mathlib

@[reducible, simp]
def smallestChange_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def smallestChange_postcond (arr : List Int) (result: Nat) (h_precond : smallestChange_precond (arr)) :=
  result = ((List.range (arr.length / 2)).filter (fun i => arr[i]! ≠ arr[arr.length - 1 - i]!)).length
