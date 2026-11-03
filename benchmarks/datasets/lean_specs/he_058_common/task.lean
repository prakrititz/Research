-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def common_precond (l1 : List Int) (l2 : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def common (l1 : List Int) (l2 : List Int) (h_precond : common_precond (l1) (l2)) : List Int :=
  -- !benchmark @start code
  ((l1.filter (fun x => x ∈ l2)).eraseDups).mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def common_postcond (l1 : List Int) (l2 : List Int) (result: List Int) (h_precond : common_precond (l1) (l2)) :=
  -- !benchmark @start postcond
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l1 ∧ x ∈ l2) ∧ (∀ x ∈ l1, x ∈ l2 → x ∈ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem common_spec_satisfied (l1 : List Int) (l2 : List Int) (h_precond : common_precond (l1) (l2)) :
    common_postcond (l1) (l2) (common (l1) (l2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
