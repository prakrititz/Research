-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def exchange_precond (lst1 : List Int) (lst2 : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def exchange (lst1 : List Int) (lst2 : List Int) (h_precond : exchange_precond (lst1) (lst2)) : String :=
  -- !benchmark @start code
  if (lst1.filter (fun x => x % 2 == 1)).length ≤ (lst2.filter (fun x => x % 2 == 0)).length then "YES" else "NO"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def exchange_postcond (lst1 : List Int) (lst2 : List Int) (result: String) (h_precond : exchange_precond (lst1) (lst2)) :=
  -- !benchmark @start postcond
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (lst1.filter (fun x => x % 2 = 1)).length ≤ (lst2.filter (fun x => x % 2 = 0)).length)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem exchange_spec_satisfied (lst1 : List Int) (lst2 : List Int) (h_precond : exchange_precond (lst1) (lst2)) :
    exchange_postcond (lst1) (lst2) (exchange (lst1) (lst2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
