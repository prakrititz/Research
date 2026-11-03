-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def reverseDelete_precond (s : String) (c : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def reverseDelete (s : String) (c : String) (h_precond : reverseDelete_precond (s) (c)) : String × Bool :=
  -- !benchmark @start code
  let t := s.toList.filter (fun ch => !(c.toList.contains ch))
  (String.mk t, t == t.reverse)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def reverseDelete_postcond (s : String) (c : String) (result: String × Bool) (h_precond : reverseDelete_precond (s) (c)) :=
  -- !benchmark @start postcond
  result.1.toList = s.toList.filter (fun ch => !(c.toList.contains ch)) ∧ (result.2 = true ↔ result.1.toList = result.1.toList.reverse)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem reverseDelete_spec_satisfied (s : String) (c : String) (h_precond : reverseDelete_precond (s) (c)) :
    reverseDelete_postcond (s) (c) (reverseDelete (s) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
