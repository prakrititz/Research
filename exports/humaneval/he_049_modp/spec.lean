import Mathlib

@[reducible, simp]
def modp_precond (n : Nat) (p : Nat) : Prop :=
  p > 0

@[reducible, simp]
def modp_postcond (n : Nat) (p : Nat) (result: Nat) (h_precond : modp_precond (n) (p)) :=
  result = 2 ^ n % p
