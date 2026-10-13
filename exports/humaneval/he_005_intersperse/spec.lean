import Mathlib

@[reducible, simp]
def intersperse_precond (numbers : List Int) (delimeter : Int) : Prop :=
  True

@[reducible, simp]
def intersperse_postcond (numbers : List Int) (delimeter : Int) (result: List Int) (h_precond : intersperse_precond (numbers) (delimeter)) :=
  result.length = (if numbers.length = 0 then 0 else 2 * numbers.length - 1) ∧
    (∀ i, i < numbers.length → result[2 * i]! = numbers[i]!) ∧
    (∀ i, i < numbers.length - 1 → result[2 * i + 1]! = delimeter)
