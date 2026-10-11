-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def carRaceCollision_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def carRaceCollision (n : Nat) (h_precond : carRaceCollision_precond (n)) : Nat :=
  -- !benchmark @start code
  n * n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def carRaceCollision_postcond (n : Nat) (result: Nat) (h_precond : carRaceCollision_precond (n)) :=
  -- !benchmark @start postcond
  result = n * n
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem carRaceCollision_spec_satisfied (n : Nat) (h_precond : carRaceCollision_precond (n)) :
    carRaceCollision_postcond (n) (carRaceCollision (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
