-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def concatenate_precond (strings : List String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def concatenate (strings : List String) (h_precond : concatenate_precond (strings)) : String :=
  -- !benchmark @start code
  strings.foldl (fun acc s => acc ++ s) ""
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def concatenate_postcond (strings : List String) (result: String) (h_precond : concatenate_precond (strings)) :=
  -- !benchmark @start postcond
  result = String.join strings
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem concatenate_spec_satisfied (strings : List String) (h_precond : concatenate_precond (strings)) :
    concatenate_postcond (strings) (concatenate (strings) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
