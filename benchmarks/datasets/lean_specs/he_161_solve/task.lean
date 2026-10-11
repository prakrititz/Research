-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def swapCase (c : Char) : Char := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
-- !benchmark @end precond_aux

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def solve (s : String) (h_precond : solve_precond (s)) : String :=
  -- !benchmark @start code
  if s.toList.any Char.isAlpha then s.map swapCase else String.mk s.toList.reverse
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def solve_postcond (s : String) (result: String) (h_precond : solve_precond (s)) :=
  -- !benchmark @start postcond
  result = (if s.toList.any Char.isAlpha then String.mk (s.toList.map swapCase) else String.mk s.toList.reverse)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem solve_spec_satisfied (s : String) (h_precond : solve_precond (s)) :
    solve_postcond (s) (solve (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
