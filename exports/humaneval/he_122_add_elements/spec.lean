import Mathlib

@[reducible, simp]
def addElements_precond (arr : List Int) (k : Nat) : Prop :=
  arr ≠ [] ∧ 1 ≤ k ∧ k ≤ arr.length

@[reducible, simp]
def addElements_postcond (arr : List Int) (k : Nat) (result: Int) (h_precond : addElements_precond (arr) (k)) :=
  result = ((arr.take k).filter (fun x => x.natAbs < 100)).sum
