-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def totalMatch_precond (lst1 : List String) (lst2 : List String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def totalMatch (lst1 : List String) (lst2 : List String) (h_precond : totalMatch_precond (lst1) (lst2)) : List String :=
  -- !benchmark @start code
  if (lst1.foldl (fun a s => a + s.length) 0) ≤ (lst2.foldl (fun a s => a + s.length) 0) then lst1 else lst2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def totalMatch_postcond (lst1 : List String) (lst2 : List String) (result: List String) (h_precond : totalMatch_precond (lst1) (lst2)) :=
  -- !benchmark @start postcond
  result = (if (lst1.map String.length).sum ≤ (lst2.map String.length).sum then lst1 else lst2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem totalMatch_spec_satisfied (lst1 : List String) (lst2 : List String) (h_precond : totalMatch_precond (lst1) (lst2)) :
    totalMatch_postcond (lst1) (lst2) (totalMatch (lst1) (lst2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
