-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sortedListSum_precond (lst : List String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortedListSum (lst : List String) (h_precond : sortedListSum_precond (lst)) : List String :=
  -- !benchmark @start code
  (lst.filter (fun s => s.length % 2 == 0)).mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortedListSum_postcond (lst : List String) (result: List String) (h_precond : sortedListSum_precond (lst)) :=
  -- !benchmark @start postcond
  List.Perm result (lst.filter (fun s => s.length % 2 = 0)) ∧
    ∀ i, i < result.length - 1 → (result[i]!.length < result[i + 1]!.length ∨ (result[i]!.length = result[i + 1]!.length ∧ ¬ (result[i + 1]! < result[i]!)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortedListSum_spec_satisfied (lst : List String) (h_precond : sortedListSum_precond (lst)) :
    sortedListSum_postcond (lst) (sortedListSum (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
