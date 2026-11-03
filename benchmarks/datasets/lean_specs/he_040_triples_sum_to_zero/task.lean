-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def triplesSumToZero_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def triplesSumToZero (l : List Int) (h_precond : triplesSumToZero_precond (l)) : Bool :=
  -- !benchmark @start code
  (List.range l.length).any (fun k => (List.range k).any (fun j => (List.range j).any (fun i => l[i]! + l[j]! + l[k]! == 0)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def triplesSumToZero_postcond (l : List Int) (result: Bool) (h_precond : triplesSumToZero_precond (l)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k, k < l.length ∧ ∃ j, j < k ∧ ∃ i, i < j ∧ l[i]! + l[j]! + l[k]! = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem triplesSumToZero_spec_satisfied (l : List Int) (h_precond : triplesSumToZero_precond (l)) :
    triplesSumToZero_postcond (l) (triplesSumToZero (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
