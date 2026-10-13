import Mathlib

@[reducible, simp]
def wordsString_precond (s : String) : Prop :=
  True

@[reducible, simp]
def wordsString_postcond (s : String) (result: List String) (h_precond : wordsString_precond (s)) :=
  result = ((s.map (fun c => if c == ',' then ' ' else c)).splitOn " ").filter (fun w => w != "")
