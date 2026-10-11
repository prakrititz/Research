-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def natOf (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
def daysIn (m : Nat) : Nat := [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]!
-- !benchmark @end precond_aux

@[reducible, simp]
def validDate_precond (date : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def validDate (date : String) (h_precond : validDate_precond (date)) : Bool :=
  -- !benchmark @start code
  let l := date.toList
  decide (l.length = 10) && l[2]! == '-' && l[5]! == '-' && (l.take 2).all Char.isDigit && ((l.drop 3).take 2).all Char.isDigit &&
    (l.drop 6).all Char.isDigit && decide (1 ≤ natOf (l.take 2)) && decide (natOf (l.take 2) ≤ 12) &&
    decide (1 ≤ natOf ((l.drop 3).take 2)) && decide (natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def validDate_postcond (date : String) (result: Bool) (h_precond : validDate_precond (date)) :=
  -- !benchmark @start postcond
  let l := date.toList
  result = true ↔ (l.length = 10 ∧ l[2]! = '-' ∧ l[5]! = '-' ∧ (l.take 2).all Char.isDigit = true ∧ ((l.drop 3).take 2).all Char.isDigit = true ∧
    (l.drop 6).all Char.isDigit = true ∧ 1 ≤ natOf (l.take 2) ∧ natOf (l.take 2) ≤ 12 ∧ 1 ≤ natOf ((l.drop 3).take 2) ∧
    natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem validDate_spec_satisfied (date : String) (h_precond : validDate_precond (date)) :
    validDate_postcond (date) (validDate (date) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
