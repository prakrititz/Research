import Mathlib

@[reducible, simp]
def countDistinctCharacters_precond (s : String) : Prop :=
  True

@[reducible, simp]
def countDistinctCharacters_postcond (s : String) (result: Nat) (h_precond : countDistinctCharacters_precond (s)) :=
  result = (s.toLower.toList.eraseDups).length
