import Mathlib

@[reducible, simp]
def makeAPile_precond (n : Nat) : Prop :=
  n > 0

@[reducible, simp]
def makeAPile_postcond (n : Nat) (result: List Nat) (h_precond : makeAPile_precond (n)) :=
  result.length = n ∧ ∀ i, i < n → result[i]! = n + 2 * i
