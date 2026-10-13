import Mathlib

@[reducible, simp]
def wordsInSentence_precond (sentence : String) : Prop :=
  True

@[reducible, simp]
def wordsInSentence_postcond (sentence : String) (result: String) (h_precond : wordsInSentence_precond (sentence)) :=
  result = " ".intercalate ((sentence.splitOn " ").filter (fun w => decide (Nat.Prime w.length)))
