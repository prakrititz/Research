import Mathlib

@[reducible, simp]
def belowThreshold_precond (l : List Int) (t : Int) : Prop :=
  True

@[reducible, simp]
def belowThreshold_postcond (l : List Int) (t : Int) (result: Bool) (h_precond : belowThreshold_precond (l) (t)) :=
  result = true ↔ ∀ x ∈ l, x < t
