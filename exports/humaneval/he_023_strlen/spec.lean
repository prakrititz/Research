import Mathlib

@[reducible, simp]
def strlen_precond (s : String) : Prop :=
  True

@[reducible, simp]
def strlen_postcond (s : String) (result: Nat) (h_precond : strlen_precond (s)) :=
  result = s.length
