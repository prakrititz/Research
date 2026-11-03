-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def nextSmallest_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def nextSmallest (lst : List Int) (h_precond : nextSmallest_precond (lst)) : Option Int :=
  -- !benchmark @start code
  (lst.eraseDups.mergeSort (fun a b => a ≤ b))[1]?
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def nextSmallest_postcond (lst : List Int) (result: Option Int) (h_precond : nextSmallest_precond (lst)) :=
  -- !benchmark @start postcond
  match result with
  | none => ∀ x ∈ lst, ∀ y ∈ lst, x = y
  | some r => r ∈ lst ∧ (∃ m ∈ lst, m < r) ∧ ∀ x ∈ lst, (∃ m ∈ lst, m < x) → r ≤ x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem nextSmallest_spec_satisfied (lst : List Int) (h_precond : nextSmallest_precond (lst)) :
    nextSmallest_postcond (lst) (nextSmallest (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
