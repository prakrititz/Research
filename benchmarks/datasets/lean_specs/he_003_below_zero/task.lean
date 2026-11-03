-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def belowZero_precond (operations : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def belowZero (operations : List Int) (h_precond : belowZero_precond (operations)) : Bool :=
  -- !benchmark @start code
  Id.run do
    let mut balance : Int := 0
    for x in operations do
      balance := balance + x
      if balance < 0 then
        return true
    return false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def belowZero_postcond (operations : List Int) (result: Bool) (h_precond : belowZero_precond (operations)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k, k ≤ operations.length ∧ (operations.take k).sum < 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem belowZero_spec_satisfied (operations : List Int) (h_precond : belowZero_precond (operations)) :
    belowZero_postcond (operations) (belowZero (operations) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
