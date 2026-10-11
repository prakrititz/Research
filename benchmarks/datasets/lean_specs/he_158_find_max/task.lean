-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def uniqChars (w : String) : Nat := w.toList.eraseDups.length
-- !benchmark @end precond_aux

@[reducible, simp]
def findMax_precond (words : List String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findMax (words : List String) (h_precond : findMax_precond (words)) : String :=
  -- !benchmark @start code
  words.foldl (fun (best : String) w => if uniqChars w > uniqChars best || (uniqChars w == uniqChars best && decide (w < best)) then w else best) ""
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findMax_postcond (words : List String) (result: String) (h_precond : findMax_precond (words)) :=
  -- !benchmark @start postcond
  (words = [] ∧ result = "") ∨ (result ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars result) ∧ ∀ w ∈ words, uniqChars w = uniqChars result → ¬ (w < result))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findMax_spec_satisfied (words : List String) (h_precond : findMax_precond (words)) :
    findMax_postcond (words) (findMax (words) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
