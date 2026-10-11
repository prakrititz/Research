-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cycpatternCheck_precond (a : String) (b : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def cycpatternCheck (a : String) (b : String) (h_precond : cycpatternCheck_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  b.length == 0 || (List.range b.length).any (fun i => (a.splitOn (String.mk (b.toList.drop i ++ b.toList.take i))).length > 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def cycpatternCheck_postcond (a : String) (b : String) (result: Bool) (h_precond : cycpatternCheck_precond (a) (b)) :=
  -- !benchmark @start postcond
  result = true ↔ (b.length = 0 ∨ ∃ i, i < b.length ∧ (b.toList.drop i ++ b.toList.take i) <:+: a.toList)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem cycpatternCheck_spec_satisfied (a : String) (b : String) (h_precond : cycpatternCheck_precond (a) (b)) :
    cycpatternCheck_postcond (a) (b) (cycpatternCheck (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
