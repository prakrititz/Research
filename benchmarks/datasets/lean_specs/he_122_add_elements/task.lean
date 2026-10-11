-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def addElements_precond (arr : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  arr ≠ [] ∧ 1 ≤ k ∧ k ≤ arr.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def addElements (arr : List Int) (k : Nat) (h_precond : addElements_precond (arr) (k)) : Int :=
  -- !benchmark @start code
  (arr.take k).foldl (fun acc x => if x.natAbs < 100 then acc + x else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def addElements_postcond (arr : List Int) (k : Nat) (result: Int) (h_precond : addElements_precond (arr) (k)) :=
  -- !benchmark @start postcond
  result = ((arr.take k).filter (fun x => x.natAbs < 100)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem addElements_spec_satisfied (arr : List Int) (k : Nat) (h_precond : addElements_precond (arr) (k)) :
    addElements_postcond (arr) (k) (addElements (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
