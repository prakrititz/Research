import Mathlib

@[reducible, simp]
def solution_precond (lst : List Int) : Prop :=
  lst ≠ []

@[reducible, simp]
def solution_postcond (lst : List Int) (result: Int) (h_precond : solution_precond (lst)) :=
  result = (((List.range lst.length).filter (fun i => i % 2 = 0 ∧ lst[i]! % 2 = 1)).map (fun i => lst[i]!)).sum
