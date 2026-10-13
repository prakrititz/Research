import Mathlib

@[reducible, simp]
def maxElement_precond (l : List Int) : Prop :=
  l ≠ []

@[reducible, simp]
def maxElement_postcond (l : List Int) (result: Int) (h_precond : maxElement_precond (l)) :=
  result ∈ l ∧ ∀ x ∈ l, x ≤ result
