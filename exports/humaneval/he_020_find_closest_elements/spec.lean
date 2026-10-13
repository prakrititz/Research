import Mathlib

@[reducible, simp]
def findClosestElements_precond (numbers : List ℚ) : Prop :=
  numbers.length ≥ 2

@[reducible, simp]
def findClosestElements_postcond (numbers : List ℚ) (result: ℚ × ℚ) (h_precond : findClosestElements_precond (numbers)) :=
  (∃ j, j < numbers.length ∧ ∃ i, i < j ∧
      ((result.1 = numbers[i]! ∧ result.2 = numbers[j]!) ∨ (result.1 = numbers[j]! ∧ result.2 = numbers[i]!))) ∧
    result.1 ≤ result.2 ∧
    ∀ j, j < numbers.length → ∀ i, i < j → result.2 - result.1 ≤ |numbers[i]! - numbers[j]!|
