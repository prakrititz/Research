-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def getPositive_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def getPositive (l : List Int) (h_precond : getPositive_precond (l)) : List Int :=
  -- !benchmark @start code
  l.foldr (fun x acc => if x > 0 then x :: acc else acc) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def getPositive_postcond (l : List Int) (result: List Int) (h_precond : getPositive_precond (l)) :=
  -- !benchmark @start postcond
  result = l.filter (fun x => x > 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem getPositive_spec_satisfied (l : List Int) (h_precond : getPositive_precond (l)) :
    getPositive_postcond (l) (getPositive (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
