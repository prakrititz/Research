import Mathlib

@[reducible, simp]
def derivative_precond (xs : List Int) : Prop :=
  True

@[reducible, simp]
def derivative_postcond (xs : List Int) (result: List Int) (h_precond : derivative_precond (xs)) :=
  result.length = xs.length - 1 ∧ ∀ i, i < xs.length - 1 → result[i]! = xs[i + 1]! * ((i : Int) + 1)
