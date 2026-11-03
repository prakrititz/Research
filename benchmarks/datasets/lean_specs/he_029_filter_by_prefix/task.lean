-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def filterByPrefix_precond (strings : List String) (prefix_ : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def filterByPrefix (strings : List String) (prefix_ : String) (h_precond : filterByPrefix_precond (strings) (prefix_)) : List String :=
  -- !benchmark @start code
  strings.foldr (fun s acc => if s.startsWith prefix_ then s :: acc else acc) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def filterByPrefix_postcond (strings : List String) (prefix_ : String) (result: List String) (h_precond : filterByPrefix_precond (strings) (prefix_)) :=
  -- !benchmark @start postcond
  result = strings.filter (fun s => s.startsWith prefix_)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem filterByPrefix_spec_satisfied (strings : List String) (prefix_ : String) (h_precond : filterByPrefix_precond (strings) (prefix_)) :
    filterByPrefix_postcond (strings) (prefix_) (filterByPrefix (strings) (prefix_) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
