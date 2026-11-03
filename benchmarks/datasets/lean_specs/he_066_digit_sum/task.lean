-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def digitSum_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def digitSum (s : String) (h_precond : digitSum_precond (s)) : Nat :=
  -- !benchmark @start code
  s.foldl (fun acc c => if c.isUpper then acc + c.toNat else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def digitSum_postcond (s : String) (result: Nat) (h_precond : digitSum_precond (s)) :=
  -- !benchmark @start postcond
  result = ((s.toList.filter Char.isUpper).map Char.toNat).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem digitSum_spec_satisfied (s : String) (h_precond : digitSum_precond (s)) :
    digitSum_postcond (s) (digitSum (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
