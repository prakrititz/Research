-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def removeDuplicates_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeDuplicates (numbers : List Int) (h_precond : removeDuplicates_precond (numbers)) : List Int :=
  -- !benchmark @start code
  numbers.foldr (fun x acc => if numbers.count x = 1 then x :: acc else acc) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def removeDuplicates_postcond (numbers : List Int) (result: List Int) (h_precond : removeDuplicates_precond (numbers)) :=
  -- !benchmark @start postcond
  result = numbers.filter (fun x => numbers.count x = 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeDuplicates_spec_satisfied (numbers : List Int) (h_precond : removeDuplicates_precond (numbers)) :
    removeDuplicates_postcond (numbers) (removeDuplicates (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
