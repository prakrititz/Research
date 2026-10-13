import Mathlib

@[reducible, simp]
def primeFib_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def primeFib_postcond (n : Nat) (result: Nat) (h_precond : primeFib_precond (n)) :=
  ∃ k, k < 300 ∧ Nat.fib k = result ∧ Nat.Prime result ∧
      (((List.range k).map Nat.fib).filter (fun m => decide (Nat.Prime m))).length = n - 1
