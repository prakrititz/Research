import Mathlib

@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse

@[reducible, simp]
def makePalindrome_precond (string : String) : Prop :=
  True

@[reducible, simp]
def makePalindrome_postcond (string : String) (result: String) (h_precond : makePalindrome_precond (string)) :=
  ∃ i, i ≤ string.length ∧ isPal (string.toList.drop i) ∧ (∀ j, j < i → ¬ isPal (string.toList.drop j)) ∧
      result.toList = string.toList ++ (string.toList.take i).reverse
