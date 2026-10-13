import Mathlib

@[reducible, simp]
def removeDuplicates_precond (numbers : List Int) : Prop :=
  True

@[reducible, simp]
def removeDuplicates_postcond (numbers : List Int) (result: List Int) (h_precond : removeDuplicates_precond (numbers)) :=
  result = numbers.filter (fun x => numbers.count x = 1)
