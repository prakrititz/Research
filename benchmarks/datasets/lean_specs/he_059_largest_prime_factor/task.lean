-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def largestPrimeFactor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 1 ∧ ¬ Nat.Prime n
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def largestPrimeFactor (n : Nat) (h_precond : largestPrimeFactor_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut m := n
    let mut i := 2
    let mut best := 1
    while i * i ≤ m do
      if m % i == 0 then
        best := i
        m := m / i
      else
        i := i + 1
    return (if m > best then m else best)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def largestPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : largestPrimeFactor_precond (n)) :=
  -- !benchmark @start postcond
  Nat.Prime result ∧ result ∣ n ∧ ∀ q, q < n + 1 → Nat.Prime q → q ∣ n → q ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem largestPrimeFactor_spec_satisfied (n : Nat) (h_precond : largestPrimeFactor_precond (n)) :
    largestPrimeFactor_postcond (n) (largestPrimeFactor (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
