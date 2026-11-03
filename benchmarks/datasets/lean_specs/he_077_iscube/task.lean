-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def iscube_precond (a : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def iscube (a : Int) (h_precond : iscube_precond (a)) : Bool :=
  -- !benchmark @start code
  (List.range (a.natAbs + 2)).any (fun k => k ^ 3 == a.natAbs)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def iscube_postcond (a : Int) (result: Bool) (h_precond : iscube_precond (a)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k, k < a.natAbs + 2 ∧ k ^ 3 = a.natAbs
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem iscube_spec_satisfied (a : Int) (h_precond : iscube_precond (a)) :
    iscube_postcond (a) (iscube (a) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
