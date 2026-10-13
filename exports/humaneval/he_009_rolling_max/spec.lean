import Mathlib

@[reducible, simp]
def rollingMax_precond (numbers : List Int) : Prop :=
  True

@[reducible, simp]
def rollingMax_postcond (numbers : List Int) (result: List Int) (h_precond : rollingMax_precond (numbers)) :=
  result.length = numbers.length ∧
    ∀ i, i < numbers.length → result[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ result[i]!
