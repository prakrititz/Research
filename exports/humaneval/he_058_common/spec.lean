import Mathlib

@[reducible, simp]
def common_precond (l1 : List Int) (l2 : List Int) : Prop :=
  True

@[reducible, simp]
def common_postcond (l1 : List Int) (l2 : List Int) (result: List Int) (h_precond : common_precond (l1) (l2)) :=
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ x ∈ result, x ∈ l1 ∧ x ∈ l2) ∧ (∀ x ∈ l1, x ∈ l2 → x ∈ result)
