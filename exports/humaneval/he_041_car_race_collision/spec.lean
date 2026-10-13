import Mathlib

@[reducible, simp]
def carRaceCollision_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def carRaceCollision_postcond (n : Nat) (result: Nat) (h_precond : carRaceCollision_precond (n)) :=
  result = n * n
