-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def stringSequence_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def stringSequence (n : Nat) (h_precond : stringSequence_precond (n)) : String :=
  -- !benchmark @start code
  " ".intercalate ((List.range (n + 1)).map (fun i => toString i))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def stringSequence_postcond (n : Nat) (result: String) (h_precond : stringSequence_precond (n)) :=
  -- !benchmark @start postcond
  result.splitOn " " = (List.range (n + 1)).map (fun i => toString i)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem stringSequence_spec_satisfied (n : Nat) (h_precond : stringSequence_precond (n)) :
    stringSequence_postcond (n) (stringSequence (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
