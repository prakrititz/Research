import Mathlib

@[reducible, simp]
def strangeSortList_precond (lst : List Int) : Prop :=
  True

@[reducible, simp]
def strangeSortList_postcond (lst : List Int) (result: List Int) (h_precond : strangeSortList_precond (lst)) :=
  let s := lst.mergeSort (fun a b => a ≤ b)
  result = (List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)
