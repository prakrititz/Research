-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def maxFill_precond (grid : List (List Nat)) (capacity : Nat) : Prop :=
  -- !benchmark @start precond
  capacity ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxFill (grid : List (List Nat)) (capacity : Nat) (h_precond : maxFill_precond (grid) (capacity)) : Nat :=
  -- !benchmark @start code
  grid.foldl (fun acc row => acc + (row.foldl (fun a x => a + x) 0 + capacity - 1) / capacity) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxFill_postcond (grid : List (List Nat)) (capacity : Nat) (result: Nat) (h_precond : maxFill_precond (grid) (capacity)) :=
  -- !benchmark @start postcond
  result = (grid.map (fun row => (row.sum + capacity - 1) / capacity)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxFill_spec_satisfied (grid : List (List Nat)) (capacity : Nat) (h_precond : maxFill_precond (grid) (capacity)) :
    maxFill_postcond (grid) (capacity) (maxFill (grid) (capacity) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
