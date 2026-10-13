import Mathlib

def natOf (cs : List Char) : Nat := cs.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
def daysIn (m : Nat) : Nat := [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]!

@[reducible, simp]
def validDate_precond (date : String) : Prop :=
  True

@[reducible, simp]
def validDate_postcond (date : String) (result: Bool) (h_precond : validDate_precond (date)) :=
  let l := date.toList
  result = true ↔ (l.length = 10 ∧ l[2]! = '-' ∧ l[5]! = '-' ∧ (l.take 2).all Char.isDigit = true ∧ ((l.drop 3).take 2).all Char.isDigit = true ∧
    (l.drop 6).all Char.isDigit = true ∧ 1 ≤ natOf (l.take 2) ∧ natOf (l.take 2) ≤ 12 ∧ 1 ≤ natOf ((l.drop 3).take 2) ∧
    natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))
