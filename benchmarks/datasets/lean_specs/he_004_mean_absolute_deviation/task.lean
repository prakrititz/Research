-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def meanAbsoluteDeviation_precond (numbers : List ℚ) : Prop :=
  -- !benchmark @start precond
  numbers ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def meanAbsoluteDeviation (numbers : List ℚ) (h_precond : meanAbsoluteDeviation_precond (numbers)) : ℚ :=
  -- !benchmark @start code
  (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℚ)|)).sum / (numbers.length : ℚ)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def meanAbsoluteDeviation_postcond (numbers : List ℚ) (result: ℚ) (h_precond : meanAbsoluteDeviation_precond (numbers)) :=
  -- !benchmark @start postcond
  |result - (numbers.map (fun x => |x - numbers.sum / (numbers.length : ℚ)|)).sum / (numbers.length : ℚ)| ≤ (1 / 1000000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem meanAbsoluteDeviation_spec_satisfied (numbers : List ℚ) (h_precond : meanAbsoluteDeviation_precond (numbers)) :
    meanAbsoluteDeviation_postcond (numbers) (meanAbsoluteDeviation (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
