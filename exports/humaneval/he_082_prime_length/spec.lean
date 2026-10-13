import Mathlib

@[reducible, simp]
def primeLength_precond (string : String) : Prop :=
  True

@[reducible, simp]
def primeLength_postcond (string : String) (result: Bool) (h_precond : primeLength_precond (string)) :=
  result = true ↔ Nat.Prime string.length
