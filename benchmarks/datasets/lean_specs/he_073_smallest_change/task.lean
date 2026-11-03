-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def smallestChange_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def smallestChange (arr : List Int) (h_precond : smallestChange_precond (arr)) : Nat :=
  -- !benchmark @start code
  (List.range (arr.length / 2)).foldl (fun acc i => if arr[i]! != arr[arr.length - 1 - i]! then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def smallestChange_postcond (arr : List Int) (result: Nat) (h_precond : smallestChange_precond (arr)) :=
  -- !benchmark @start postcond
  result = ((List.range (arr.length / 2)).filter (fun i => arr[i]! ≠ arr[arr.length - 1 - i]!)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem smallestChange_spec_satisfied (arr : List Int) (h_precond : smallestChange_precond (arr)) :
    smallestChange_postcond (arr) (smallestChange (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
