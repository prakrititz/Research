import Mathlib

@[reducible, simp]
def reverseDelete_precond (s : String) (c : String) : Prop :=
  True

@[reducible, simp]
def reverseDelete_postcond (s : String) (c : String) (result: String × Bool) (h_precond : reverseDelete_precond (s) (c)) :=
  result.1.toList = s.toList.filter (fun ch => !(c.toList.contains ch)) ∧ (result.2 = true ↔ result.1.toList = result.1.toList.reverse)
