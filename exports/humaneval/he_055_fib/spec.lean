import Mathlib

@[reducible, simp]
def fib_precond (n : Nat) : Prop :=
  True

@[simp] def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibSpec n + fibSpec (n + 1)

@[reducible, simp]
def fib_postcond (n : Nat) (result: Nat) (h_precond : fib_precond (n)) :=
  result = fibSpec n
