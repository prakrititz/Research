-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def search_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst ≠ [] ∧ ∀ x ∈ lst, x > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def search (lst : List Nat) (h_precond : search_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.foldl (fun best x => if lst.count x ≥ x && (x : Int) > best then (x : Int) else best) (-1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def search_postcond (lst : List Nat) (result: Int) (h_precond : search_precond (lst)) :=
  -- !benchmark @start postcond
  (result = -1 ∧ ∀ x ∈ lst, lst.count x < x) ∨
    (result > 0 ∧ result.toNat ∈ lst ∧ lst.count result.toNat ≥ result.toNat ∧ ∀ x ∈ lst, lst.count x ≥ x → x ≤ result.toNat)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem search_spec_satisfied (lst : List Nat) (h_precond : search_precond (lst)) :
    search_postcond (lst) (search (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
