-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def maximum_precond (arr : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ arr.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maximum (arr : List Int) (k : Nat) (h_precond : maximum_precond (arr) (k)) : List Int :=
  -- !benchmark @start code
  ((arr.mergeSort (fun a b => a ≥ b)).take k).mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maximum_postcond (arr : List Int) (k : Nat) (result: List Int) (h_precond : maximum_precond (arr) (k)) :=
  -- !benchmark @start postcond
  result.isPerm ((arr.mergeSort (fun a b => a ≥ b)).take k) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maximum_spec_satisfied (arr : List Int) (k : Nat) (h_precond : maximum_precond (arr) (k)) :
    maximum_postcond (arr) (k) (maximum (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
