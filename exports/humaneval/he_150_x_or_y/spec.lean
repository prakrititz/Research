import Mathlib

@[reducible, simp]
def xOrY_precond (n : Nat) (x : Int) (y : Int) : Prop :=
  True

@[reducible, simp] def primeSpec (n : Nat) : Prop := n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0

@[reducible, simp]
def xOrY_postcond (n : Nat) (x : Int) (y : Int) (result: Int) (h_precond : xOrY_precond (n) (x) (y)) :=
  (primeSpec n → result = x) ∧ (¬ primeSpec n → result = y)
