import Mathlib

@[reducible, simp]
def sameChars_precond (s0 : String) (s1 : String) : Prop :=
  True

@[reducible, simp]
def sameChars_postcond (s0 : String) (s1 : String) (result: Bool) (h_precond : sameChars_precond (s0) (s1)) :=
  result = true ↔ ((∀ c ∈ s0.toList, c ∈ s1.toList) ∧ (∀ c ∈ s1.toList, c ∈ s0.toList))
