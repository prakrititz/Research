-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def f106_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def f106 (n : Nat) (h_precond : f106_precond (n)) : List Nat :=
  -- !benchmark @start code
  (List.range n).map (fun i => if (i + 1) % 2 == 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def f106_postcond (n : Nat) (result: List Nat) (h_precond : f106_precond (n)) :=
  -- !benchmark @start postcond
  result.length = n ∧ ∀ i, i < n → result[i]! = (if (i + 1) % 2 = 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem f106_spec_satisfied (n : Nat) (h_precond : f106_precond (n)) :
    f106_postcond (n) (f106 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
