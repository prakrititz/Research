-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def solution_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def solution (lst : List Int) (h_precond : solution_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.zipIdx.foldl (fun acc (x, i) => if i % 2 == 0 && x % 2 == 1 then acc + x else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def solution_postcond (lst : List Int) (result: Int) (h_precond : solution_precond (lst)) :=
  -- !benchmark @start postcond
  result = (((List.range lst.length).filter (fun i => i % 2 = 0 ∧ lst[i]! % 2 = 1)).map (fun i => lst[i]!)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem solution_spec_satisfied (lst : List Int) (h_precond : solution_precond (lst)) :
    solution_postcond (lst) (solution (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
