-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def pairsSumToZero_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def pairsSumToZero (l : List Int) (h_precond : pairsSumToZero_precond (l)) : Bool :=
  -- !benchmark @start code
  (List.range l.length).any (fun j => (List.range j).any (fun i => l[i]! + l[j]! == 0))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def pairsSumToZero_postcond (l : List Int) (result: Bool) (h_precond : pairsSumToZero_precond (l)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ j, j < l.length ∧ ∃ i, i < j ∧ l[i]! + l[j]! = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem pairsSumToZero_spec_satisfied (l : List Int) (h_precond : pairsSumToZero_precond (l)) :
    pairsSumToZero_postcond (l) (pairsSumToZero (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
