-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def makeAPile_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def makeAPile (n : Nat) (h_precond : makeAPile_precond (n)) : List Nat :=
  -- !benchmark @start code
  (List.range n).map (fun i => n + 2 * i)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def makeAPile_postcond (n : Nat) (result: List Nat) (h_precond : makeAPile_precond (n)) :=
  -- !benchmark @start postcond
  result.length = n ∧ ∀ i, i < n → result[i]! = n + 2 * i
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem makeAPile_spec_satisfied (n : Nat) (h_precond : makeAPile_precond (n)) :
    makeAPile_postcond (n) (makeAPile (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
