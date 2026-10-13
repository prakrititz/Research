import Mathlib

@[reducible, simp] def hasSub (s t : String) : Prop :=
  ∃ i, i ≤ s.length ∧ t.toList = (s.toList.drop i).take t.length

@[reducible, simp]
def filterBySubstring_precond (strings : List String) (substring : String) : Prop :=
  True

@[reducible, simp]
def filterBySubstring_postcond (strings : List String) (substring : String) (result: List String) (h_precond : filterBySubstring_precond (strings) (substring)) :=
  result = strings.filter (fun s => decide (hasSub s substring))
