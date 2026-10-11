-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  -- !benchmark @start code
  if n < 2 then false else (List.range n).all (fun d => d < 2 || n % d != 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  -- !benchmark @start postcond
  result = true ↔ (n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPrime_spec_satisfied (n : Nat) (h_precond : isPrime_precond (n)) :
    isPrime_postcond (n) (isPrime (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
