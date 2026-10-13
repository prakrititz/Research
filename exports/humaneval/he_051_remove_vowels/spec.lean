import Mathlib

@[reducible, simp]
def removeVowels_precond (text : String) : Prop :=
  True

@[reducible, simp]
def removeVowels_postcond (text : String) (result: String) (h_precond : removeVowels_precond (text)) :=
  result.toList = text.toList.filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))
