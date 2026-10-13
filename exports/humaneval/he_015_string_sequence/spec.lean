import Mathlib

@[reducible, simp]
def stringSequence_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def stringSequence_postcond (n : Nat) (result: String) (h_precond : stringSequence_precond (n)) :=
  result.splitOn " " = (List.range (n + 1)).map (fun i => toString i)
