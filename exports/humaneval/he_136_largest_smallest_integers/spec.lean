import Mathlib

@[reducible, simp]
def largestSmallestIntegers_precond (lst : List Int) : Prop :=
  True

@[reducible, simp]
def largestSmallestIntegers_postcond (lst : List Int) (result: Option Int × Option Int) (h_precond : largestSmallestIntegers_precond (lst)) :=
  ((result.1 = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ a ∈ lst, result.1 = some a ∧ a < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ a)) ∧
    ((result.2 = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ b ∈ lst, result.2 = some b ∧ 0 < b ∧ ∀ x ∈ lst, 0 < x → b ≤ x))
