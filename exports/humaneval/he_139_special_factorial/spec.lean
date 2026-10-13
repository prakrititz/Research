import Mathlib

@[reducible, simp]
def specialFactorial_precond (n : Nat) : Prop :=
  n > 0

@[simp] def factSpec : Nat → Nat
  | 0 => 1
  | (n + 1) => (n + 1) * factSpec n

@[reducible, simp]
def specialFactorial_postcond (n : Nat) (result: Nat) (h_precond : specialFactorial_precond (n)) :=
  result = ((List.range n).map (fun i => factSpec (i + 1))).prod
