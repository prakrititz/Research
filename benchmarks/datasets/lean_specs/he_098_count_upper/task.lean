-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countUpper_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countUpper (s : String) (h_precond : countUpper_precond (s)) : Nat :=
  -- !benchmark @start code
  s.toList.zipIdx.foldl (fun acc (c, i) => if i % 2 == 0 && (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U') then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countUpper_postcond (s : String) (result: Nat) (h_precond : countUpper_precond (s)) :=
  -- !benchmark @start postcond
  result = ((List.range s.length).filter (fun i => i % 2 = 0 ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'])).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countUpper_spec_satisfied (s : String) (h_precond : countUpper_precond (s)) :
    countUpper_postcond (s) (countUpper (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
