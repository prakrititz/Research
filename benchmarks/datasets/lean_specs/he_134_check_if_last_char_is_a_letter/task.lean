-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def checkIfLastCharIsALetter_precond (txt : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def checkIfLastCharIsALetter (txt : String) (h_precond : checkIfLastCharIsALetter_precond (txt)) : Bool :=
  -- !benchmark @start code
  match txt.toList.reverse with
  | [] => false
  | [c] => c.isAlpha
  | c :: d :: _ => c.isAlpha && d == ' '
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def checkIfLastCharIsALetter_postcond (txt : String) (result: Bool) (h_precond : checkIfLastCharIsALetter_precond (txt)) :=
  -- !benchmark @start postcond
  result = true ↔ (txt.length ≥ 1 ∧ txt.toList[txt.length - 1]!.isAlpha = true ∧ (txt.length = 1 ∨ txt.toList[txt.length - 2]! = ' '))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem checkIfLastCharIsALetter_spec_satisfied (txt : String) (h_precond : checkIfLastCharIsALetter_precond (txt)) :
    checkIfLastCharIsALetter_postcond (txt) (checkIfLastCharIsALetter (txt) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
