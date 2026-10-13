import Mathlib

def isVowelC (c : Char) : Bool := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c
@[reducible, simp] def goodAt (w : List Char) (i : Nat) : Prop :=
  1 ≤ i ∧ i + 1 < w.length ∧ isVowelC w[i]! = true ∧ isVowelC w[i - 1]! = false ∧ isVowelC w[i + 1]! = false

@[reducible, simp]
def getClosestVowel_precond (word : String) : Prop :=
  True

@[reducible, simp]
def getClosestVowel_postcond (word : String) (result: String) (h_precond : getClosestVowel_precond (word)) :=
  let w := word.toList
  (result = "" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧
  (result ≠ "" → ∃ i, i < w.length ∧ goodAt w i ∧ result = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j)
