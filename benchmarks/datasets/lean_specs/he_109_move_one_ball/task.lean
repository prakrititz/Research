-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def moveOneBall_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def moveOneBall (arr : List Int) (h_precond : moveOneBall_precond (arr)) : Bool :=
  -- !benchmark @start code
  (List.range (arr.length + 1)).any (fun i => arr.drop i ++ arr.take i == arr.mergeSort (fun a b => a ≤ b))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def moveOneBall_postcond (arr : List Int) (result: Bool) (h_precond : moveOneBall_precond (arr)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ i, i < arr.length + 1 ∧ arr.drop i ++ arr.take i = arr.mergeSort (fun a b => a ≤ b)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem moveOneBall_spec_satisfied (arr : List Int) (h_precond : moveOneBall_precond (arr)) :
    moveOneBall_postcond (arr) (moveOneBall (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
