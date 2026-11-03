-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSorted_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  ∀ x ∈ lst, x ≥ 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isSorted (lst : List Int) (h_precond : isSorted_precond (lst)) : Bool :=
  -- !benchmark @start code
  (List.range (lst.length - 1)).all (fun i => lst[i]! ≤ lst[i + 1]!) && lst.all (fun x => lst.count x ≤ 2)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isSorted_postcond (lst : List Int) (result: Bool) (h_precond : isSorted_precond (lst)) :=
  -- !benchmark @start postcond
  result = true ↔ ((∀ i, i < lst.length - 1 → lst[i]! ≤ lst[i + 1]!) ∧ ∀ x ∈ lst, lst.count x ≤ 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isSorted_spec_satisfied (lst : List Int) (h_precond : isSorted_precond (lst)) :
    isSorted_postcond (lst) (isSorted (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
