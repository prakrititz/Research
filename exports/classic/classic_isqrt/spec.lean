import Mathlib

@[reducible, simp]
def isqrt_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def isqrt_postcond (n : Nat) (result: Nat) (h_precond : isqrt_precond (n)) :=
  result * result ≤ n ∧ n < (result + 1) * (result + 1)
