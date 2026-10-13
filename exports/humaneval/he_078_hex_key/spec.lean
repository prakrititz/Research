import Mathlib

@[reducible, simp]
def hexKey_precond (num : String) : Prop :=
  True

@[reducible, simp]
def hexKey_postcond (num : String) (result: Nat) (h_precond : hexKey_precond (num)) :=
  result = (num.toList.filter (fun c => ['2', '3', '5', '7', 'B', 'D'].contains c)).length
