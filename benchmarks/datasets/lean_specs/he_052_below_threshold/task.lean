-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def belowThreshold_precond (l : List Int) (t : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def belowThreshold (l : List Int) (t : Int) (h_precond : belowThreshold_precond (l) (t)) : Bool :=
  -- !benchmark @start code
  l.all (fun x => x < t)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def belowThreshold_postcond (l : List Int) (t : Int) (result: Bool) (h_precond : belowThreshold_precond (l) (t)) :=
  -- !benchmark @start postcond
  result = true ↔ ∀ x ∈ l, x < t
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem belowThreshold_spec_satisfied (l : List Int) (t : Int) (h_precond : belowThreshold_precond (l) (t)) :
    belowThreshold_postcond (l) (t) (belowThreshold (l) (t) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
