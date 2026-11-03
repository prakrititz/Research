-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def incrList_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def incrList (l : List Int) (h_precond : incrList_precond (l)) : List Int :=
  -- !benchmark @start code
  l.map (fun x => x + 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def incrList_postcond (l : List Int) (result: List Int) (h_precond : incrList_precond (l)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧ ∀ i, i < l.length → result[i]! = l[i]! + 1
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem incrList_spec_satisfied (l : List Int) (h_precond : incrList_precond (l)) :
    incrList_postcond (l) (incrList (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
