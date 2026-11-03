-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def howManyTimes_precond (string : String) (substring : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def howManyTimes (string : String) (substring : String) (h_precond : howManyTimes_precond (string) (substring)) : Nat :=
  -- !benchmark @start code
  (List.range string.length).foldl (fun acc i => if substring.toList.isPrefixOf (string.toList.drop i) then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def howManyTimes_postcond (string : String) (substring : String) (result: Nat) (h_precond : howManyTimes_precond (string) (substring)) :=
  -- !benchmark @start postcond
  result = ((List.range string.length).filter (fun i => substring.toList.isPrefixOf (string.toList.drop i))).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem howManyTimes_spec_satisfied (string : String) (substring : String) (h_precond : howManyTimes_precond (string) (substring)) :
    howManyTimes_postcond (string) (substring) (howManyTimes (string) (substring) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
