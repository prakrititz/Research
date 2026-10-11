-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def add_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def add (x : Int) (y : Int) (h_precond : add_precond (x) (y)) : Int :=
  -- !benchmark @start code
  x + y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def add_postcond (x : Int) (y : Int) (result: Int) (h_precond : add_precond (x) (y)) :=
  -- !benchmark @start postcond
  result = x + y
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem add_spec_satisfied (x : Int) (y : Int) (h_precond : add_precond (x) (y)) :
    add_postcond (x) (y) (add (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
