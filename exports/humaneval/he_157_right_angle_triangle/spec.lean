import Mathlib

@[reducible, simp]
def rightAngleTriangle_precond (a : Nat) (b : Nat) (c : Nat) : Prop :=
  True

@[reducible, simp]
def rightAngleTriangle_postcond (a : Nat) (b : Nat) (c : Nat) (result: Bool) (h_precond : rightAngleTriangle_precond (a) (b) (c)) :=
  result = true ↔ (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a)
