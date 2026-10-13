import Mathlib

@[reducible, simp]
def triangleArea_precond (a : ℚ) (h : ℚ) : Prop :=
  True

@[reducible, simp]
def triangleArea_postcond (a : ℚ) (h : ℚ) (result: ℚ) (h_precond : triangleArea_precond (a) (h)) :=
  |result - a * h / 2| ≤ (1 / 1000000 : ℚ)
