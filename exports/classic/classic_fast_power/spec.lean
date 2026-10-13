import Mathlib

@[reducible, simp]
def fastPower_precond (b : Int) (e : Nat) : Prop :=
  True

@[reducible, simp]
def fastPower_postcond (b : Int) (e : Nat) (result: Int) (h_precond : fastPower_precond (b) (e)) :=
  result = b ^ e
