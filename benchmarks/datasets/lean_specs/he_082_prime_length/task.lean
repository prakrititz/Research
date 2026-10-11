-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def primeLength_precond (string : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def primeLength (string : String) (h_precond : primeLength_precond (string)) : Bool :=
  -- !benchmark @start code
  decide (Nat.Prime string.length)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def primeLength_postcond (string : String) (result: Bool) (h_precond : primeLength_precond (string)) :=
  -- !benchmark @start postcond
  result = true ↔ Nat.Prime string.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem primeLength_spec_satisfied (string : String) (h_precond : primeLength_precond (string)) :
    primeLength_postcond (string) (primeLength (string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
