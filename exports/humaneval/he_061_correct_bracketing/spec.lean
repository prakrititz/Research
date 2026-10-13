import Mathlib

@[reducible, simp]
def correctBracketing_precond (brackets : String) : Prop :=
  True

@[reducible, simp]
def correctBracketing_postcond (brackets : String) (result: Bool) (h_precond : correctBracketing_precond (brackets)) :=
  result = true ↔ ((∀ k, k ≤ brackets.length → (brackets.toList.take k).count '(' ≥ (brackets.toList.take k).count ')') ∧ brackets.toList.count '(' = brackets.toList.count ')')
