import Mathlib

@[reducible, simp]
def isEqualToSumEven_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def isEqualToSumEven_postcond (n : Nat) (result: Bool) (h_precond : isEqualToSumEven_precond (n)) :=
  result = true ↔ (n ≥ 8 ∧ n % 2 = 0)
