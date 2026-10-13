import Mathlib

def numName (x : Int) : String :=
  if x = 1 then "One" else if x = 2 then "Two" else if x = 3 then "Three" else if x = 4 then "Four" else if x = 5 then "Five"
  else if x = 6 then "Six" else if x = 7 then "Seven" else if x = 8 then "Eight" else "Nine"

@[reducible, simp]
def byLength_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def byLength_postcond (arr : List Int) (result: List String) (h_precond : byLength_precond (arr)) :=
  let ds := arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)
  result = (ds.mergeSort (fun a b => a ≥ b)).map numName
