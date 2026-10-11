-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasCloseElements_precond (numbers : List ℚ) (threshold : ℚ) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasCloseElements (numbers : List ℚ) (threshold : ℚ) (h_precond : hasCloseElements_precond (numbers) (threshold)) : Bool :=
  -- !benchmark @start code
  (List.range numbers.length).any (fun j => (List.range j).any (fun i => decide (|numbers[i]! - numbers[j]!| < threshold)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasCloseElements_postcond (numbers : List ℚ) (threshold : ℚ) (result: Bool) (h_precond : hasCloseElements_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ j, j < numbers.length ∧ ∃ i, i < j ∧ |numbers[i]! - numbers[j]!| < threshold
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasCloseElements_spec_satisfied (numbers : List ℚ) (threshold : ℚ) (h_precond : hasCloseElements_precond (numbers) (threshold)) :
    hasCloseElements_postcond (numbers) (threshold) (hasCloseElements (numbers) (threshold) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
