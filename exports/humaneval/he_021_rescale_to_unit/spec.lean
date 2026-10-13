import Mathlib

@[reducible, simp]
def rescaleToUnit_precond (numbers : List ℚ) : Prop :=
  numbers.length ≥ 2 ∧ numbers.foldl min numbers[0]! < numbers.foldl max numbers[0]!

@[reducible, simp]
def rescaleToUnit_postcond (numbers : List ℚ) (result: List ℚ) (h_precond : rescaleToUnit_precond (numbers)) :=
  result.length = numbers.length ∧ ∀ i, i < numbers.length →
      |result[i]! - (numbers[i]! - numbers.foldl min numbers[0]!) / (numbers.foldl max numbers[0]! - numbers.foldl min numbers[0]!)| ≤ (1 / 1000000 : ℚ)
