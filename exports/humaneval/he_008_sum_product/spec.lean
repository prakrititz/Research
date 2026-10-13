import Mathlib

@[reducible, simp]
def sumProduct_precond (numbers : List Int) : Prop :=
  True

@[reducible, simp]
def sumProduct_postcond (numbers : List Int) (result: Int × Int) (h_precond : sumProduct_precond (numbers)) :=
  result.1 = numbers.sum ∧ result.2 = numbers.prod
