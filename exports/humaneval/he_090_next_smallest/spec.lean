import Mathlib

@[reducible, simp]
def nextSmallest_precond (lst : List Int) : Prop :=
  True

@[reducible, simp]
def nextSmallest_postcond (lst : List Int) (result: Option Int) (h_precond : nextSmallest_precond (lst)) :=
  match result with
  | none => ∀ x ∈ lst, ∀ y ∈ lst, x = y
  | some r => r ∈ lst ∧ (∃ m ∈ lst, m < r) ∧ ∀ x ∈ lst, (∃ m ∈ lst, m < x) → r ≤ x
