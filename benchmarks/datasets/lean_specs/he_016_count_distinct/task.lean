-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countDistinctCharacters_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countDistinctCharacters (s : String) (h_precond : countDistinctCharacters_precond (s)) : Nat :=
  -- !benchmark @start code
  (s.toLower.toList.foldl (fun acc c => if c ∈ acc then acc else c :: acc) []).length
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countDistinctCharacters_postcond (s : String) (result: Nat) (h_precond : countDistinctCharacters_precond (s)) :=
  -- !benchmark @start postcond
  result = (s.toLower.toList.eraseDups).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countDistinctCharacters_spec_satisfied (s : String) (h_precond : countDistinctCharacters_precond (s)) :
    countDistinctCharacters_postcond (s) (countDistinctCharacters (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
