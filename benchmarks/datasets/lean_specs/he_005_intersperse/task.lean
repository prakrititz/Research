-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def intersperse_precond (numbers : List Int) (delimeter : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def intersperse (numbers : List Int) (delimeter : Int) (h_precond : intersperse_precond (numbers) (delimeter)) : List Int :=
  -- !benchmark @start code
  numbers.intersperse delimeter
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def intersperse_postcond (numbers : List Int) (delimeter : Int) (result: List Int) (h_precond : intersperse_precond (numbers) (delimeter)) :=
  -- !benchmark @start postcond
  result.length = (if numbers.length = 0 then 0 else 2 * numbers.length - 1) ∧
    (∀ i, i < numbers.length → result[2 * i]! = numbers[i]!) ∧
    (∀ i, i < numbers.length - 1 → result[2 * i + 1]! = delimeter)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem intersperse_spec_satisfied (numbers : List Int) (delimeter : Int) (h_precond : intersperse_precond (numbers) (delimeter)) :
    intersperse_postcond (numbers) (delimeter) (intersperse (numbers) (delimeter) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
