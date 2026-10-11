-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def truncateNumber_precond (number : ℚ) : Prop :=
  -- !benchmark @start precond
  number ≥ 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def truncateNumber (number : ℚ) (h_precond : truncateNumber_precond (number)) : ℚ :=
  -- !benchmark @start code
  number - (⌊number⌋ : ℚ)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def truncateNumber_postcond (number : ℚ) (result: ℚ) (h_precond : truncateNumber_precond (number)) :=
  -- !benchmark @start postcond
  |result - (number - (⌊number⌋ : ℚ))| ≤ (1 / 1000000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem truncateNumber_spec_satisfied (number : ℚ) (h_precond : truncateNumber_precond (number)) :
    truncateNumber_postcond (number) (truncateNumber (number) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
