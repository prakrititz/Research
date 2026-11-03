-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def strlen_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def strlen (s : String) (h_precond : strlen_precond (s)) : Nat :=
  -- !benchmark @start code
  s.toList.length
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def strlen_postcond (s : String) (result: Nat) (h_precond : strlen_precond (s)) :=
  -- !benchmark @start postcond
  result = s.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem strlen_spec_satisfied (s : String) (h_precond : strlen_precond (s)) :
    strlen_postcond (s) (strlen (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
