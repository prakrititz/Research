-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def digits_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def digits (n : Nat) (h_precond : digits_precond (n)) : Nat :=
  -- !benchmark @start code
  let ds := (toString n).toList.map (fun c => c.toNat - 48)
  if ds.any (fun d => d % 2 == 1) then (ds.filter (fun d => d % 2 == 1)).foldl (fun a d => a * d) 1 else 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def digits_postcond (n : Nat) (result: Nat) (h_precond : digits_precond (n)) :=
  -- !benchmark @start postcond
  let ds := (toString n).toList.map (fun c => c.toNat - 48)
  result = (if ds.any (fun d => d % 2 = 1) then (ds.filter (fun d => d % 2 = 1)).prod else 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem digits_spec_satisfied (n : Nat) (h_precond : digits_precond (n)) :
    digits_postcond (n) (digits (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
