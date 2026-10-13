import Mathlib

@[reducible, simp]
def unique_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def unique_postcond (l : List Int) (result: List Int) (h_precond : unique_precond (l)) :=
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l) ∧ (∀ x ∈ l, x ∈ result)
