import Mathlib

@[reducible, simp]
def isPalindrome_precond (text : String) : Prop :=
  True

@[reducible, simp]
def isPalindrome_postcond (text : String) (result: Bool) (h_precond : isPalindrome_precond (text)) :=
  result = true ↔ ∀ i, i < text.length → text.toList[i]! = text.toList[text.length - 1 - i]!
