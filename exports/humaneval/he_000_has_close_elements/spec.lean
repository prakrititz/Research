import Mathlib

@[reducible, simp]
def hasCloseElements_precond (numbers : List ℚ) (threshold : ℚ) : Prop :=
  True

@[reducible, simp]
def hasCloseElements_postcond (numbers : List ℚ) (threshold : ℚ) (result: Bool) (h_precond : hasCloseElements_precond (numbers) (threshold)) :=
  result = true ↔ ∃ j, j < numbers.length ∧ ∃ i, i < j ∧ |numbers[i]! - numbers[j]!| < threshold
