import Mathlib

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  True

@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  result = ((a.natAbs % 10 : Nat) : Int) * ((b.natAbs % 10 : Nat) : Int)
