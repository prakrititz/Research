import Mathlib

@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  result = true ↔ (n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0)
