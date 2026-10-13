import Mathlib

@[reducible, simp]
def circularShift_precond (x : Nat) (shift : Nat) : Prop :=
  True

@[reducible, simp]
def circularShift_postcond (x : Nat) (shift : Nat) (result: String) (h_precond : circularShift_precond (x) (shift)) :=
  let d := (toString x).toList
  let n := d.length
  result.toList = (if shift > n then d.reverse else d.drop (n - shift % n) ++ d.take (n - shift % n))
