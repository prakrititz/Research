import Mathlib

@[reducible, simp]
def iscube_precond (a : Int) : Prop :=
  True

@[reducible, simp]
def iscube_postcond (a : Int) (result: Bool) (h_precond : iscube_precond (a)) :=
  result = true ↔ ∃ k, k < a.natAbs + 2 ∧ k ^ 3 = a.natAbs
