-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def xOrY_precond (n : Nat) (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def xOrY (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond (n) (x) (y)) : Int :=
  -- !benchmark @start code
  if n ≥ 2 && (List.range n).all (fun d => d < 2 || n % d != 0) then x else y
  -- !benchmark @end code


-- !benchmark @start postcond_aux
@[reducible, simp] def primeSpec (n : Nat) : Prop := n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0
-- !benchmark @end postcond_aux


@[reducible, simp]
def xOrY_postcond (n : Nat) (x : Int) (y : Int) (result: Int) (h_precond : xOrY_precond (n) (x) (y)) :=
  -- !benchmark @start postcond
  (primeSpec n → result = x) ∧ (¬ primeSpec n → result = y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem xOrY_spec_satisfied (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond (n) (x) (y)) :
    xOrY_postcond (n) (x) (y) (xOrY (n) (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
