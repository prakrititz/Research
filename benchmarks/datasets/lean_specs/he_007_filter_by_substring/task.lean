-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def hasSub (s t : String) : Prop :=
  ∃ i, i ≤ s.length ∧ t.toList = (s.toList.drop i).take t.length
-- !benchmark @end precond_aux

@[reducible, simp]
def filterBySubstring_precond (strings : List String) (substring : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def filterBySubstring (strings : List String) (substring : String) (h_precond : filterBySubstring_precond (strings) (substring)) : List String :=
  -- !benchmark @start code
  strings.foldr (fun s acc => if (List.range (s.length + 1)).any (fun i => substring.toList.isPrefixOf (s.toList.drop i)) then s :: acc else acc) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def filterBySubstring_postcond (strings : List String) (substring : String) (result: List String) (h_precond : filterBySubstring_precond (strings) (substring)) :=
  -- !benchmark @start postcond
  result = strings.filter (fun s => decide (hasSub s substring))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem filterBySubstring_spec_satisfied (strings : List String) (substring : String) (h_precond : filterBySubstring_precond (strings) (substring)) :
    filterBySubstring_postcond (strings) (substring) (filterBySubstring (strings) (substring) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
