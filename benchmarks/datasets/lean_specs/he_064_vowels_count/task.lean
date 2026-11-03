-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def vowelsCount_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def vowelsCount (s : String) (h_precond : vowelsCount_precond (s)) : Nat :=
  -- !benchmark @start code
  (s.toList.foldl (fun acc c => if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c then acc + 1 else acc) 0) +
    (if s.toList.getLast? == some 'y' || s.toList.getLast? == some 'Y' then 1 else 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def vowelsCount_postcond (s : String) (result: Nat) (h_precond : vowelsCount_precond (s)) :=
  -- !benchmark @start postcond
  result = (s.toList.filter (fun c => ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)).length +
      (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem vowelsCount_spec_satisfied (s : String) (h_precond : vowelsCount_precond (s)) :
    vowelsCount_postcond (s) (vowelsCount (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
