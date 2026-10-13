import Mathlib

@[reducible, simp]
def checkIfLastCharIsALetter_precond (txt : String) : Prop :=
  True

@[reducible, simp]
def checkIfLastCharIsALetter_postcond (txt : String) (result: Bool) (h_precond : checkIfLastCharIsALetter_precond (txt)) :=
  result = true ↔ (txt.length ≥ 1 ∧ txt.toList[txt.length - 1]!.isAlpha = true ∧ (txt.length = 1 ∨ txt.toList[txt.length - 2]! = ' '))
