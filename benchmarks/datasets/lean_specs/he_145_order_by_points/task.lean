-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def digitWeight (x : Int) : Int :=
  let ds : List Nat := (toString x.natAbs).toList.map (fun c => c.toNat - 48)
  let s : Int := (ds.map (fun d => (d : Int))).sum
  if x < 0 then s - 2 * ((ds.head! : Nat) : Int) else s
-- !benchmark @end precond_aux

@[reducible, simp]
def orderByPoints_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def orderByPoints (nums : List Int) (h_precond : orderByPoints_precond (nums)) : List Int :=
  -- !benchmark @start code
  nums.mergeSort (fun a b => digitWeight a ≤ digitWeight b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def orderByPoints_postcond (nums : List Int) (result: List Int) (h_precond : orderByPoints_precond (nums)) :=
  -- !benchmark @start postcond
  result.length = nums.length ∧ (∀ i, i < result.length - 1 → digitWeight result[i]! ≤ digitWeight result[i + 1]!) ∧
    ∀ x ∈ nums, result.filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem orderByPoints_spec_satisfied (nums : List Int) (h_precond : orderByPoints_precond (nums)) :
    orderByPoints_postcond (nums) (orderByPoints (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
