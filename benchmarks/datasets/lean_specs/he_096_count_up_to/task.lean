-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countUpTo_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countUpTo (n : Nat) (h_precond : countUpTo_precond (n)) : List Nat :=
  -- !benchmark @start code
  (List.range n).filter (fun p => decide (Nat.Prime p))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countUpTo_postcond (n : Nat) (result: List Nat) (h_precond : countUpTo_precond (n)) :=
  -- !benchmark @start postcond
  (∀ p ∈ result, p < n ∧ Nat.Prime p) ∧ (∀ p, p < n → Nat.Prime p → p ∈ result) ∧ ∀ i, i < result.length - 1 → result[i]! < result[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countUpTo_spec_satisfied (n : Nat) (h_precond : countUpTo_precond (n)) :
    countUpTo_postcond (n) (countUpTo (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
