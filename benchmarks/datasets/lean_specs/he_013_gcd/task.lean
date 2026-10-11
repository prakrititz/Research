-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def greatestCommonDivisor_precond (a : Nat) (b : Nat) : Prop :=
  -- !benchmark @start precond
  a > 0 ∧ b > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def greatestCommonDivisor (a : Nat) (b : Nat) (h_precond : greatestCommonDivisor_precond (a) (b)) : Nat :=
  -- !benchmark @start code
  Nat.gcd a b
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def greatestCommonDivisor_postcond (a : Nat) (b : Nat) (result: Nat) (h_precond : greatestCommonDivisor_precond (a) (b)) :=
  -- !benchmark @start postcond
  result > 0 ∧ a % result = 0 ∧ b % result = 0 ∧ ∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem greatestCommonDivisor_spec_satisfied (a : Nat) (b : Nat) (h_precond : greatestCommonDivisor_precond (a) (b)) :
    greatestCommonDivisor_postcond (a) (b) (greatestCommonDivisor (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
