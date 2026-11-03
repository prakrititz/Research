-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def skjkasdkd_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  ∃ x ∈ lst, Nat.Prime x
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def skjkasdkd (lst : List Nat) (h_precond : skjkasdkd_precond (lst)) : Nat :=
  -- !benchmark @start code
  let p := (lst.filter (fun x => decide (Nat.Prime x))).foldl max 0
  ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def skjkasdkd_postcond (lst : List Nat) (result: Nat) (h_precond : skjkasdkd_precond (lst)) :=
  -- !benchmark @start postcond
  ∃ p ∈ lst, Nat.Prime p ∧ (∀ x ∈ lst, Nat.Prime x → x ≤ p) ∧ result = ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem skjkasdkd_spec_satisfied (lst : List Nat) (h_precond : skjkasdkd_precond (lst)) :
    skjkasdkd_postcond (lst) (skjkasdkd (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
