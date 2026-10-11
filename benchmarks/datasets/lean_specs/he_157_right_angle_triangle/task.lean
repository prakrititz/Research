-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rightAngleTriangle_precond (a : Nat) (b : Nat) (c : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rightAngleTriangle (a : Nat) (b : Nat) (c : Nat) (h_precond : rightAngleTriangle_precond (a) (b) (c)) : Bool :=
  -- !benchmark @start code
  a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rightAngleTriangle_postcond (a : Nat) (b : Nat) (c : Nat) (result: Bool) (h_precond : rightAngleTriangle_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  result = true ↔ (a * a + b * b = c * c ∨ a * a + c * c = b * b ∨ b * b + c * c = a * a)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rightAngleTriangle_spec_satisfied (a : Nat) (b : Nat) (c : Nat) (h_precond : rightAngleTriangle_precond (a) (b) (c)) :
    rightAngleTriangle_postcond (a) (b) (c) (rightAngleTriangle (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
