-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def strangeSortList_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def strangeSortList (lst : List Int) (h_precond : strangeSortList_precond (lst)) : List Int :=
  -- !benchmark @start code
  let s := lst.mergeSort (fun a b => a ≤ b)
  (List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def strangeSortList_postcond (lst : List Int) (result: List Int) (h_precond : strangeSortList_precond (lst)) :=
  -- !benchmark @start postcond
  let s := lst.mergeSort (fun a b => a ≤ b)
  result = (List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem strangeSortList_spec_satisfied (lst : List Int) (h_precond : strangeSortList_precond (lst)) :
    strangeSortList_postcond (lst) (strangeSortList (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
