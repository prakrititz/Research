-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def factorize_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def factorize (n : Nat) (h_precond : factorize_precond (n)) : List Nat :=
  -- !benchmark @start code
  Id.run do
    let mut m := n
    let mut i := 2
    let mut fact : List Nat := []
    while i * i ≤ m do
      if m % i == 0 then
        fact := fact ++ [i]
        m := m / i
      else
        i := i + 1
    if m > 1 then fact := fact ++ [m]
    return fact
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def factorize_postcond (n : Nat) (result: List Nat) (h_precond : factorize_precond (n)) :=
  -- !benchmark @start postcond
  result.prod = n ∧ (∀ p ∈ result, Nat.Prime p) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem factorize_spec_satisfied (n : Nat) (h_precond : factorize_precond (n)) :
    factorize_postcond (n) (factorize (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
