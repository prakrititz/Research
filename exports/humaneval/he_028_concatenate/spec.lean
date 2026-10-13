import Mathlib

@[reducible, simp]
def concatenate_precond (strings : List String) : Prop :=
  True

@[reducible, simp]
def concatenate_postcond (strings : List String) (result: String) (h_precond : concatenate_precond (strings)) :=
  result = String.join strings
