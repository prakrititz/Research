-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def canArrange_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  arr.Nodup
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def canArrange (arr : List Int) (h_precond : canArrange_precond (arr)) : Int :=
  -- !benchmark @start code
  Id.run do
    let mut ans : Int := -1
    for i in [1:arr.length] do
      if arr[i]! < arr[i - 1]! then ans := (i : Int)
    return ans
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def canArrange_postcond (arr : List Int) (result: Int) (h_precond : canArrange_precond (arr)) :=
  -- !benchmark @start postcond
  (result = -1 ∧ ∀ i, i < arr.length → 1 ≤ i → arr[i - 1]! ≤ arr[i]!) ∨
    (∃ i, i < arr.length ∧ 1 ≤ i ∧ result = (i : Int) ∧ arr[i]! < arr[i - 1]! ∧ ∀ j, j < arr.length → i < j → arr[j - 1]! ≤ arr[j]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem canArrange_spec_satisfied (arr : List Int) (h_precond : canArrange_precond (arr)) :
    canArrange_postcond (arr) (canArrange (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
