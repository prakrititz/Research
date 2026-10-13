import Mathlib

def swapCase (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  True

@[reducible, simp]
def solve_postcond (s : String) (result: String) (h_precond : solve_precond (s)) :=
  result = (if s.toList.any Char.isAlpha then String.mk (s.toList.map swapCase) else String.mk s.toList.reverse)
