-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEqualToSumEven_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isEqualToSumEven (n : Nat) (h_precond : isEqualToSumEven_precond (n)) : Bool :=
  -- !benchmark @start code
  n ≥ 8 && n % 2 == 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEqualToSumEven_postcond (n : Nat) (result: Bool) (h_precond : isEqualToSumEven_precond (n)) :=
  -- !benchmark @start postcond
  result = true ↔ (n ≥ 8 ∧ n % 2 = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEqualToSumEven_spec_satisfied (n : Nat) (h_precond : isEqualToSumEven_precond (n)) :
    isEqualToSumEven_postcond (n) (isEqualToSumEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
