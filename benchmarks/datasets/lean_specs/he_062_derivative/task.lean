-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def derivative_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def derivative (xs : List Int) (h_precond : derivative_precond (xs)) : List Int :=
  -- !benchmark @start code
  (xs.zipIdx.map (fun (x, i) => x * (i : Int))).drop 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def derivative_postcond (xs : List Int) (result: List Int) (h_precond : derivative_precond (xs)) :=
  -- !benchmark @start postcond
  result.length = xs.length - 1 ∧ ∀ i, i < xs.length - 1 → result[i]! = xs[i + 1]! * ((i : Int) + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem derivative_spec_satisfied (xs : List Int) (h_precond : derivative_precond (xs)) :
    derivative_postcond (xs) (derivative (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
