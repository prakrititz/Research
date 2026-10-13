import Mathlib

@[reducible, simp]
def startsOneEnds_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def startsOneEnds_postcond (n : Nat) (result: Nat) (h_precond : startsOneEnds_precond (n)) :=
  result = ((List.range (10 ^ n)).filter (fun m => 10 ^ (n - 1) ≤ m ∧ (m / 10 ^ (n - 1) = 1 ∨ m % 10 = 1))).length
