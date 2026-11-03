-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def removeVowels_precond (text : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeVowels (text : String) (h_precond : removeVowels_precond (text)) : String :=
  -- !benchmark @start code
  String.mk (text.toList.filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def removeVowels_postcond (text : String) (result: String) (h_precond : removeVowels_precond (text)) :=
  -- !benchmark @start postcond
  result.toList = text.toList.filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeVowels_spec_satisfied (text : String) (h_precond : removeVowels_precond (text)) :
    removeVowels_postcond (text) (removeVowels (text) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
