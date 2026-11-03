-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def chooseNum_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def chooseNum (x : Int) (y : Int) (h_precond : chooseNum_precond (x) (y)) : Int :=
  -- !benchmark @start code
  if x > y then -1 else if y % 2 == 0 then y else if y - 1 ≥ x then y - 1 else -1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def chooseNum_postcond (x : Int) (y : Int) (result: Int) (h_precond : chooseNum_precond (x) (y)) :=
  -- !benchmark @start postcond
  (result = -1 ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 ≠ 0) ∨
    (result % 2 = 0 ∧ x ≤ result ∧ result ≤ y ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 = 0 → x + (k : Int) ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem chooseNum_spec_satisfied (x : Int) (y : Int) (h_precond : chooseNum_precond (x) (y)) :
    chooseNum_postcond (x) (y) (chooseNum (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
