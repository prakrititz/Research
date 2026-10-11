-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def flipChar (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
-- !benchmark @end precond_aux

@[reducible, simp]
def flipCase_precond (string : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def flipCase (string : String) (h_precond : flipCase_precond (string)) : String :=
  -- !benchmark @start code
  String.mk (string.toList.map flipChar)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def flipCase_postcond (string : String) (result: String) (h_precond : flipCase_precond (string)) :=
  -- !benchmark @start postcond
  result.length = string.length ∧ ∀ i, i < string.length → result.toList[i]! = flipChar string.toList[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem flipCase_spec_satisfied (string : String) (h_precond : flipCase_precond (string)) :
    flipCase_postcond (string) (flipCase (string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
