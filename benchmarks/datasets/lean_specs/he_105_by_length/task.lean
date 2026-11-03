-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def numName (x : Int) : String :=
  if x = 1 then "One" else if x = 2 then "Two" else if x = 3 then "Three" else if x = 4 then "Four" else if x = 5 then "Five"
  else if x = 6 then "Six" else if x = 7 then "Seven" else if x = 8 then "Eight" else "Nine"

-- !benchmark @end precond_aux

@[reducible, simp]
def byLength_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def byLength (arr : List Int) (h_precond : byLength_precond (arr)) : List String :=
  -- !benchmark @start code
  ((arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (fun a b => a ≥ b)).map numName
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def byLength_postcond (arr : List Int) (result: List String) (h_precond : byLength_precond (arr)) :=
  -- !benchmark @start postcond
  let ds := arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)
  result = (ds.mergeSort (fun a b => a ≥ b)).map numName
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem byLength_spec_satisfied (arr : List Int) (h_precond : byLength_precond (arr)) :
    byLength_postcond (arr) (byLength (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
