import Mathlib

@[reducible, simp]
def digits_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def digits_postcond (n : Nat) (result: Nat) (h_precond : digits_precond (n)) :=
  let ds := (toString n).toList.map (fun c => c.toNat - 48)
  result = (if ds.any (fun d => d % 2 = 1) then (ds.filter (fun d => d % 2 = 1)).prod else 0)
