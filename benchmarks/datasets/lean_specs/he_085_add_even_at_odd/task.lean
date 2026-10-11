-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def addEvenAtOdd_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def addEvenAtOdd (lst : List Int) (h_precond : addEvenAtOdd_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.zipIdx.foldl (fun acc (x, i) => if i % 2 == 1 && x % 2 == 0 then acc + x else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def addEvenAtOdd_postcond (lst : List Int) (result: Int) (h_precond : addEvenAtOdd_precond (lst)) :=
  -- !benchmark @start postcond
  result = (((List.range lst.length).filter (fun i => i % 2 = 1 ∧ lst[i]! % 2 = 0)).map (fun i => lst[i]!)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem addEvenAtOdd_spec_satisfied (lst : List Int) (h_precond : addEvenAtOdd_precond (lst)) :
    addEvenAtOdd_postcond (lst) (addEvenAtOdd (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
