import Mathlib

def signedDigitSum (x : Int) : Int :=
  let ds := (toString x.natAbs).toList.map (fun c => ((c.toNat - 48 : Nat) : Int))
  if x < 0 then (ds.tail).sum - ds.head! else ds.sum

@[reducible, simp]
def countNums_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def countNums_postcond (arr : List Int) (result: Nat) (h_precond : countNums_precond (arr)) :=
  result = (arr.filter (fun x => signedDigitSum x > 0)).length
