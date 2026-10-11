-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def signedDigitSum (x : Int) : Int :=
  let ds := (toString x.natAbs).toList.map (fun c => ((c.toNat - 48 : Nat) : Int))
  if x < 0 then (ds.tail).sum - ds.head! else ds.sum
-- !benchmark @end precond_aux

@[reducible, simp]
def countNums_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countNums (arr : List Int) (h_precond : countNums_precond (arr)) : Nat :=
  -- !benchmark @start code
  arr.foldl (fun acc x => if signedDigitSum x > 0 then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countNums_postcond (arr : List Int) (result: Nat) (h_precond : countNums_precond (arr)) :=
  -- !benchmark @start postcond
  result = (arr.filter (fun x => signedDigitSum x > 0)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countNums_spec_satisfied (arr : List Int) (h_precond : countNums_precond (arr)) :
    countNums_postcond (arr) (countNums (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
