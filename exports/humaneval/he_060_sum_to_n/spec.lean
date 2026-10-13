import Mathlib

@[reducible, simp]
def sumToN_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def sumToN_postcond (n : Nat) (result: Nat) (h_precond : sumToN_precond (n)) :=
  2 * result = n * (n + 1)
