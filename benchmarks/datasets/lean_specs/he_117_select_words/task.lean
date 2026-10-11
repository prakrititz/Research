-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def selectWords_precond (s : String) (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def selectWords (s : String) (n : Nat) (h_precond : selectWords_precond (s) (n)) : List String :=
  -- !benchmark @start code
  (s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains ch))).length == n)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def selectWords_postcond (s : String) (n : Nat) (result: List String) (h_precond : selectWords_precond (s) (n)) :=
  -- !benchmark @start postcond
  result = (s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains ch))).length == n)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem selectWords_spec_satisfied (s : String) (n : Nat) (h_precond : selectWords_precond (s) (n)) :
    selectWords_postcond (s) (n) (selectWords (s) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
