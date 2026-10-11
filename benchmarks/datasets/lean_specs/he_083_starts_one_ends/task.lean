-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def startsOneEnds_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def startsOneEnds (n : Nat) (h_precond : startsOneEnds_precond (n)) : Nat :=
  -- !benchmark @start code
  if n == 1 then 1 else 18 * 10 ^ (n - 2)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def startsOneEnds_postcond (n : Nat) (result: Nat) (h_precond : startsOneEnds_precond (n)) :=
  -- !benchmark @start postcond
  result = ((List.range (10 ^ n)).filter (fun m => 10 ^ (n - 1) ≤ m ∧ (m / 10 ^ (n - 1) = 1 ∨ m % 10 = 1))).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem startsOneEnds_spec_satisfied (n : Nat) (h_precond : startsOneEnds_precond (n)) :
    startsOneEnds_postcond (n) (startsOneEnds (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
