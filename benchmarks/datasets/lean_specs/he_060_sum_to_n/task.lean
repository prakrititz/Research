-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumToN_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumToN (n : Nat) (h_precond : sumToN_precond (n)) : Nat :=
  -- !benchmark @start code
  (List.range (n + 1)).sum
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumToN_postcond (n : Nat) (result: Nat) (h_precond : sumToN_precond (n)) :=
  -- !benchmark @start postcond
  2 * result = n * (n + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumToN_spec_satisfied (n : Nat) (h_precond : sumToN_precond (n)) :
    sumToN_postcond (n) (sumToN (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
