-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sqrtApprox_precond (N : ℚ) (e : ℚ) : Prop :=
  -- !benchmark @start precond
  N ≥ 0 ∧ e > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sqrtApprox (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond (N) (e)) : ℚ :=
  -- !benchmark @start code
  Id.run do
    let mut x : ℚ := 0
    while (x + e) * (x + e) ≤ N do
      x := x + e
    return x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sqrtApprox_postcond (N : ℚ) (e : ℚ) (result: ℚ) (h_precond : sqrtApprox_precond (N) (e)) :=
  -- !benchmark @start postcond
  result ≥ 0 ∧ result * result ≤ N ∧ N < (result + e) * (result + e)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sqrtApprox_spec_satisfied (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond (N) (e)) :
    sqrtApprox_postcond (N) (e) (sqrtApprox (N) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
