-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumSquaresIdx_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumSquaresIdx (lst : List Int) (h_precond : sumSquaresIdx_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.zipIdx.foldl (fun acc (x, i) => if i % 3 == 0 then acc + x ^ 2 else if i % 4 == 0 then acc + x ^ 3 else acc + x) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumSquaresIdx_postcond (lst : List Int) (result: Int) (h_precond : sumSquaresIdx_precond (lst)) :=
  -- !benchmark @start postcond
  result = ((List.range lst.length).map (fun i => if i % 3 = 0 then lst[i]! ^ 2 else if i % 4 = 0 then lst[i]! ^ 3 else lst[i]!)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumSquaresIdx_spec_satisfied (lst : List Int) (h_precond : sumSquaresIdx_precond (lst)) :
    sumSquaresIdx_postcond (lst) (sumSquaresIdx (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
