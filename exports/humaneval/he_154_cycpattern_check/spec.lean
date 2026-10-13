import Mathlib

@[reducible, simp]
def cycpatternCheck_precond (a : String) (b : String) : Prop :=
  True

@[reducible, simp]
def cycpatternCheck_postcond (a : String) (b : String) (result: Bool) (h_precond : cycpatternCheck_precond (a) (b)) :=
  result = true ↔ (b.length = 0 ∨ ∃ i, i < b.length ∧ (b.toList.drop i ++ b.toList.take i) <:+: a.toList)
