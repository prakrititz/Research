-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def allPrefixes_precond (string : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def allPrefixes (string : String) (h_precond : allPrefixes_precond (string)) : List String :=
  -- !benchmark @start code
  (List.range string.length).map (fun i => String.mk (string.toList.take (i + 1)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def allPrefixes_postcond (string : String) (result: List String) (h_precond : allPrefixes_precond (string)) :=
  -- !benchmark @start postcond
  result.length = string.length ∧ ∀ i, i < string.length → result[i]! = String.mk (string.toList.take (i + 1))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem allPrefixes_spec_satisfied (string : String) (h_precond : allPrefixes_precond (string)) :
    allPrefixes_postcond (string) (allPrefixes (string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
