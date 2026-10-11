-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse
-- !benchmark @end precond_aux

@[reducible, simp]
def makePalindrome_precond (string : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def makePalindrome (string : String) (h_precond : makePalindrome_precond (string)) : String :=
  -- !benchmark @start code
  let l := string.toList
  let i := ((List.range (l.length + 1)).find? (fun i => l.drop i == (l.drop i).reverse)).getD 0
  String.mk (l ++ (l.take i).reverse)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def makePalindrome_postcond (string : String) (result: String) (h_precond : makePalindrome_precond (string)) :=
  -- !benchmark @start postcond
  ∃ i, i ≤ string.length ∧ isPal (string.toList.drop i) ∧ (∀ j, j < i → ¬ isPal (string.toList.drop j)) ∧
      result.toList = string.toList ++ (string.toList.take i).reverse
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem makePalindrome_spec_satisfied (string : String) (h_precond : makePalindrome_precond (string)) :
    makePalindrome_postcond (string) (makePalindrome (string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
