-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def wordsString_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def wordsString (s : String) (h_precond : wordsString_precond (s)) : List String :=
  -- !benchmark @start code
  ((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def wordsString_postcond (s : String) (result: List String) (h_precond : wordsString_precond (s)) :=
  -- !benchmark @start postcond
  result = ((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem wordsString_spec_satisfied (s : String) (h_precond : wordsString_precond (s)) :
    wordsString_postcond (s) (wordsString (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
