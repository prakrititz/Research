import Mathlib

@[reducible, simp]
def addEvenAtOdd_precond (lst : List Int) : Prop :=
  lst ≠ []

@[reducible, simp]
def addEvenAtOdd_postcond (lst : List Int) (result: Int) (h_precond : addEvenAtOdd_precond (lst)) :=
  result = (((List.range lst.length).filter (fun i => i % 2 = 1 ∧ lst[i]! % 2 = 0)).map (fun i => lst[i]!)).sum
