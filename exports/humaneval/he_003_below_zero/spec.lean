import Mathlib

@[reducible, simp]
def belowZero_precond (operations : List Int) : Prop :=
  True

@[reducible, simp]
def belowZero_postcond (operations : List Int) (result: Bool) (h_precond : belowZero_precond (operations)) :=
  result = true ↔ ∃ k, k ≤ operations.length ∧ (operations.take k).sum < 0
