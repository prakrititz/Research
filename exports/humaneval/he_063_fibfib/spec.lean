import Mathlib

def fibfibSpec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => fibfibSpec (n + 2) + fibfibSpec (n + 1) + fibfibSpec n

@[reducible, simp]
def fibfib_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def fibfib_postcond (n : Nat) (result: Nat) (h_precond : fibfib_precond (n)) :=
  result = fibfibSpec n
