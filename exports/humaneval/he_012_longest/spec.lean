import Mathlib

@[reducible, simp]
def longest_precond (strings : List String) : Prop :=
  True

@[reducible, simp]
def longest_postcond (strings : List String) (result: Option String) (h_precond : longest_precond (strings)) :=
  match result with
    | none => strings = []
    | some s => ∃ i, i < strings.length ∧ strings[i]! = s ∧ (∀ t ∈ strings, t.length ≤ s.length) ∧
        ∀ j, j < i → strings[j]!.length < s.length
