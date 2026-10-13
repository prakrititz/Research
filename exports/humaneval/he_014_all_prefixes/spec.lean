import Mathlib

@[reducible, simp]
def allPrefixes_precond (string : String) : Prop :=
  True

@[reducible, simp]
def allPrefixes_postcond (string : String) (result: List String) (h_precond : allPrefixes_precond (string)) :=
  result.length = string.length ∧ ∀ i, i < string.length → result[i]! = String.mk (string.toList.take (i + 1))
