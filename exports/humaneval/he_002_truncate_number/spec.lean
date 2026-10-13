import Mathlib

@[reducible, simp]
def truncateNumber_precond (number : ℚ) : Prop :=
  number ≥ 0

@[reducible, simp]
def truncateNumber_postcond (number : ℚ) (result: ℚ) (h_precond : truncateNumber_precond (number)) :=
  |result - (number - (⌊number⌋ : ℚ))| ≤ (1 / 1000000 : ℚ)
