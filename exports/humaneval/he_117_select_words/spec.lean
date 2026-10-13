import Mathlib

@[reducible, simp]
def selectWords_precond (s : String) (n : Nat) : Prop :=
  True

@[reducible, simp]
def selectWords_postcond (s : String) (n : Nat) (result: List String) (h_precond : selectWords_precond (s) (n)) :=
  result = (s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains ch))).length == n)
