import Mathlib

@[reducible, simp]
def isBored_precond (S : String) : Prop :=
  True

@[reducible, simp]
def isBored_postcond (S : String) (result: Nat) (h_precond : isBored_precond (S)) :=
  let sentences := (((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim
  result = (sentences.filter (fun t => t.startsWith "I ")).length
