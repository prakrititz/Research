import Mathlib

@[reducible, simp]
def totalMatch_precond (lst1 : List String) (lst2 : List String) : Prop :=
  True

@[reducible, simp]
def totalMatch_postcond (lst1 : List String) (lst2 : List String) (result: List String) (h_precond : totalMatch_precond (lst1) (lst2)) :=
  result = (if (lst1.map String.length).sum ≤ (lst2.map String.length).sum then lst1 else lst2)
