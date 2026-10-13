import Mathlib

@[reducible, simp]
def countUpper_precond (s : String) : Prop :=
  True

@[reducible, simp]
def countUpper_postcond (s : String) (result: Nat) (h_precond : countUpper_precond (s)) :=
  result = ((List.range s.length).filter (fun i => i % 2 = 0 ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'])).length
