import Mathlib

def fib4Spec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | (n + 4) => fib4Spec (n + 3) + fib4Spec (n + 2) + fib4Spec (n + 1) + fib4Spec n

@[reducible, simp]
def fib4_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def fib4_postcond (n : Nat) (result: Nat) (h_precond : fib4_precond (n)) :=
  result = fib4Spec n
