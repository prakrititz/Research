-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def fastPower_precond (b : Int) (e : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fastPower (b : Int) (e : Nat) (h_precond : fastPower_precond (b) (e)) : Int :=
  -- !benchmark @start code
  b ^ e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fastPower_postcond (b : Int) (e : Nat) (result: Int) (h_precond : fastPower_precond (b) (e)) :=
  -- !benchmark @start postcond
  result = b ^ e
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fastPower_spec_satisfied (b : Int) (e : Nat) (h_precond : fastPower_precond (b) (e)) :
    fastPower_postcond (b) (e) (fastPower (b) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
