-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isqrt_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isqrt (n : Nat) (h_precond : isqrt_precond (n)) : Nat :=
  -- !benchmark @start code
  Nat.sqrt n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isqrt_postcond (n : Nat) (result: Nat) (h_precond : isqrt_precond (n)) :=
  -- !benchmark @start postcond
  result * result ≤ n ∧ n < (result + 1) * (result + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isqrt_spec_satisfied (n : Nat) (h_precond : isqrt_precond (n)) :
    isqrt_postcond (n) (isqrt (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
