import Mathlib

@[reducible, simp]
def filterByPrefix_precond (strings : List String) (prefix_ : String) : Prop :=
  True

@[reducible, simp]
def filterByPrefix_postcond (strings : List String) (prefix_ : String) (result: List String) (h_precond : filterByPrefix_precond (strings) (prefix_)) :=
  result = strings.filter (fun s => s.startsWith prefix_)
