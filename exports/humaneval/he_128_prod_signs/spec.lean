import Mathlib

@[reducible, simp]
def prodSigns_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def prodSigns_postcond (arr : List Int) (result: Option Int) (h_precond : prodSigns_precond (arr)) :=
  match result with
  | none => arr = []
  | some r => arr ≠ [] ∧ r = (arr.map (fun (x : Int) => (x.natAbs : Int))).sum * (arr.map Int.sign).prod
