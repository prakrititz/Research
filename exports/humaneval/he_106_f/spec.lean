import Mathlib

@[reducible, simp]
def f106_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def f106_postcond (n : Nat) (result: List Nat) (h_precond : f106_precond (n)) :=
  result.length = n ∧ ∀ i, i < n → result[i]! = (if (i + 1) % 2 = 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2)
