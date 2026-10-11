-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isMultiplyPrime_precond (a : Nat) : Prop :=
  -- !benchmark @start precond
  a < 100
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isMultiplyPrime (a : Nat) (h_precond : isMultiplyPrime_precond (a)) : Bool :=
  -- !benchmark @start code
  Id.run do
    let mut m := a
    let mut count := 0
    let mut i := 2
    while i ≤ m do
      if m % i == 0 then
        m := m / i
        count := count + 1
      else
        i := i + 1
    return a > 1 && count == 3
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isMultiplyPrime_postcond (a : Nat) (result: Bool) (h_precond : isMultiplyPrime_precond (a)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ p, p < a + 1 ∧ ∃ q, q < a + 1 ∧ ∃ r, r < a + 1 ∧ p * q * r = a ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isMultiplyPrime_spec_satisfied (a : Nat) (h_precond : isMultiplyPrime_precond (a)) :
    isMultiplyPrime_postcond (a) (isMultiplyPrime (a) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
