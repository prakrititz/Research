import Mathlib

def flipChar (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c

@[reducible, simp]
def flipCase_precond (string : String) : Prop :=
  True

@[reducible, simp]
def flipCase_postcond (string : String) (result: String) (h_precond : flipCase_precond (string)) :=
  result.length = string.length ∧ ∀ i, i < string.length → result.toList[i]! = flipChar string.toList[i]!
