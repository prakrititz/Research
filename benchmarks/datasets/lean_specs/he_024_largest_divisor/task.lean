-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def largestDivisor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def largestDivisor (n : Nat) (h_precond : largestDivisor_precond (n)) : Nat :=
  -- !benchmark @start code
  ((List.range n).filter (fun d => d > 0 && n % d == 0)).getLast?.getD 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def largestDivisor_postcond (n : Nat) (result: Nat) (h_precond : largestDivisor_precond (n)) :=
  -- !benchmark @start postcond
  result > 0 ∧ result < n ∧ n % result = 0 ∧ ∀ d, d < n → result < d → n % d ≠ 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem largestDivisor_spec_satisfied (n : Nat) (h_precond : largestDivisor_precond (n)) :
    largestDivisor_postcond (n) (largestDivisor (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
