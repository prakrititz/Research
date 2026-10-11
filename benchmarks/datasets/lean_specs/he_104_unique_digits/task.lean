-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def noEvenDigit (n : Nat) : Bool := (toString n).toList.all (fun c => (c.toNat - 48) % 2 == 1)
-- !benchmark @end precond_aux

@[reducible, simp]
def uniqueDigits_precond (x : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def uniqueDigits (x : List Nat) (h_precond : uniqueDigits_precond (x)) : List Nat :=
  -- !benchmark @start code
  (x.filter noEvenDigit).mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def uniqueDigits_postcond (x : List Nat) (result: List Nat) (h_precond : uniqueDigits_precond (x)) :=
  -- !benchmark @start postcond
  result.isPerm (x.filter noEvenDigit) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem uniqueDigits_spec_satisfied (x : List Nat) (h_precond : uniqueDigits_precond (x)) :
    uniqueDigits_postcond (x) (uniqueDigits (x) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
