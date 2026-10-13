import Mathlib

@[reducible, simp]
def meanAbsoluteDeviation_precond (numbers : List ℚ) : Prop :=
  numbers ≠ []

@[reducible, simp]
def meanAbsoluteDeviation_postcond (numbers : List ℚ) (result: ℚ) (h_precond : meanAbsoluteDeviation_precond (numbers)) :=
  |result - (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℚ)|)).sum / (numbers.length : ℚ)| ≤ (1 / 1000000 : ℚ)
