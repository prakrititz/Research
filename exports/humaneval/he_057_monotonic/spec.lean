import Mathlib

@[reducible, simp]
def monotonic_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def monotonic_postcond (l : List Int) (result: Bool) (h_precond : monotonic_precond (l)) :=
  result = true ↔ ((∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) ∨ (∀ i, i < l.length - 1 → l[i]! ≥ l[i + 1]!))
