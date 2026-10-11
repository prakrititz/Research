-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPalindrome_precond (text : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPalindrome (text : String) (h_precond : isPalindrome_precond (text)) : Bool :=
  -- !benchmark @start code
  text.toList == text.toList.reverse
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPalindrome_postcond (text : String) (result: Bool) (h_precond : isPalindrome_precond (text)) :=
  -- !benchmark @start postcond
  result = true ↔ ∀ i, i < text.length → text.toList[i]! = text.toList[text.length - 1 - i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPalindrome_spec_satisfied (text : String) (h_precond : isPalindrome_precond (text)) :
    isPalindrome_postcond (text) (isPalindrome (text) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
