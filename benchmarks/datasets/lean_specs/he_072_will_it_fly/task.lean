-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def willItFly_precond (q : List Int) (w : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def willItFly (q : List Int) (w : Int) (h_precond : willItFly_precond (q) (w)) : Bool :=
  -- !benchmark @start code
  q.reverse == q && decide (q.sum ≤ w)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def willItFly_postcond (q : List Int) (w : Int) (result: Bool) (h_precond : willItFly_precond (q) (w)) :=
  -- !benchmark @start postcond
  result = true ↔ ((∀ i, i < q.length → q[i]! = q[q.length - 1 - i]!) ∧ q.sum ≤ w)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem willItFly_spec_satisfied (q : List Int) (w : Int) (h_precond : willItFly_precond (q) (w)) :
    willItFly_postcond (q) (w) (willItFly (q) (w) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
