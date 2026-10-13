import Mathlib

@[reducible, simp]
def isSorted_precond (lst : List Int) : Prop :=
  ∀ x ∈ lst, x ≥ 0

@[reducible, simp]
def isSorted_postcond (lst : List Int) (result: Bool) (h_precond : isSorted_precond (lst)) :=
  result = true ↔ ((∀ i, i < lst.length - 1 → lst[i]! ≤ lst[i + 1]!) ∧ ∀ x ∈ lst, lst.count x ≤ 2)
