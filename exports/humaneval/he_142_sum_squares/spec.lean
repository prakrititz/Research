import Mathlib

@[reducible, simp]
def sumSquaresIdx_precond (lst : List Int) : Prop :=
  True

@[reducible, simp]
def sumSquaresIdx_postcond (lst : List Int) (result: Int) (h_precond : sumSquaresIdx_precond (lst)) :=
  result = ((List.range lst.length).map (fun i => if i % 3 = 0 then lst[i]! ^ 2 else if i % 4 = 0 then lst[i]! ^ 3 else lst[i]!)).sum
