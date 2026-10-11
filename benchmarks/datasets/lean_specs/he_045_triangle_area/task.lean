-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def triangleArea_precond (a : ℚ) (h : ℚ) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def triangleArea (a : ℚ) (h : ℚ) (h_precond : triangleArea_precond (a) (h)) : ℚ :=
  -- !benchmark @start code
  a * h / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def triangleArea_postcond (a : ℚ) (h : ℚ) (result: ℚ) (h_precond : triangleArea_precond (a) (h)) :=
  -- !benchmark @start postcond
  |result - a * h / 2| ≤ (1 / 1000000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem triangleArea_spec_satisfied (a : ℚ) (h : ℚ) (h_precond : triangleArea_precond (a) (h)) :
    triangleArea_postcond (a) (h) (triangleArea (a) (h) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
