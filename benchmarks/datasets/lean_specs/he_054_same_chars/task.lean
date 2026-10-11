-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sameChars_precond (s0 : String) (s1 : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sameChars (s0 : String) (s1 : String) (h_precond : sameChars_precond (s0) (s1)) : Bool :=
  -- !benchmark @start code
  s0.toList.all (fun c => s1.toList.contains c) && s1.toList.all (fun c => s0.toList.contains c)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sameChars_postcond (s0 : String) (s1 : String) (result: Bool) (h_precond : sameChars_precond (s0) (s1)) :=
  -- !benchmark @start postcond
  result = true ↔ ((∀ c ∈ s0.toList, c ∈ s1.toList) ∧ (∀ c ∈ s1.toList, c ∈ s0.toList))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sameChars_spec_satisfied (s0 : String) (s1 : String) (h_precond : sameChars_precond (s0) (s1)) :
    sameChars_postcond (s0) (s1) (sameChars (s0) (s1) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
