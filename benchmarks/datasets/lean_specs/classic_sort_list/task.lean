-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sortList_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortList (l : List Int) (h_precond : sortList_precond (l)) : List Int :=
  -- !benchmark @start code
  l.mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortList_postcond (l : List Int) (result: List Int) (h_precond : sortList_precond (l)) :=
  -- !benchmark @start postcond
  (∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧ result.isPerm l
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortList_spec_satisfied (l : List Int) (h_precond : sortList_precond (l)) :
    sortList_postcond (l) (sortList (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
