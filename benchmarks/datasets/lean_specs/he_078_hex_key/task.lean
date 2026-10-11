-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hexKey_precond (num : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hexKey (num : String) (h_precond : hexKey_precond (num)) : Nat :=
  -- !benchmark @start code
  num.toList.foldl (fun acc c => if ['2', '3', '5', '7', 'B', 'D'].contains c then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hexKey_postcond (num : String) (result: Nat) (h_precond : hexKey_precond (num)) :=
  -- !benchmark @start postcond
  result = (num.toList.filter (fun c => ['2', '3', '5', '7', 'B', 'D'].contains c)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hexKey_spec_satisfied (num : String) (h_precond : hexKey_precond (num)) :
    hexKey_postcond (num) (hexKey (num) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
