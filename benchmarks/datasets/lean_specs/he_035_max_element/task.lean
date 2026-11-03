-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def maxElement_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  l ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxElement (l : List Int) (h_precond : maxElement_precond (l)) : Int :=
  -- !benchmark @start code
  l.foldl max l.head!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxElement_postcond (l : List Int) (result: Int) (h_precond : maxElement_precond (l)) :=
  -- !benchmark @start postcond
  result ∈ l ∧ ∀ x ∈ l, x ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxElement_spec_satisfied (l : List Int) (h_precond : maxElement_precond (l)) :
    maxElement_postcond (l) (maxElement (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
