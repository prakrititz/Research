import Mathlib

def uniqChars (w : String) : Nat := w.toList.eraseDups.length

@[reducible, simp]
def findMax_precond (words : List String) : Prop :=
  True

@[reducible, simp]
def findMax_postcond (words : List String) (result: String) (h_precond : findMax_precond (words)) :=
  (words = [] ∧ result = "") ∨ (result ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars result) ∧ ∀ w ∈ words, uniqChars w = uniqChars result → ¬ (w < result))
