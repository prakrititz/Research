-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def unique_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def unique (l : List Int) (h_precond : unique_precond (l)) : List Int :=
  -- !benchmark @start code
  (l.eraseDups).mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def unique_postcond (l : List Int) (result: List Int) (h_precond : unique_precond (l)) :=
  -- !benchmark @start postcond
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l) ∧ (∀ x ∈ l, x ∈ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem unique_spec_satisfied (l : List Int) (h_precond : unique_precond (l)) :
    unique_postcond (l) (unique (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
