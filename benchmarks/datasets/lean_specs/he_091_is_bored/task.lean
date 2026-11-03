-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isBored_precond (S : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isBored (S : String) (h_precond : isBored_precond (S)) : Nat :=
  -- !benchmark @start code
  (((((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim).filter (fun t => t.startsWith "I ")).length
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isBored_postcond (S : String) (result: Nat) (h_precond : isBored_precond (S)) :=
  -- !benchmark @start postcond
  let sentences := (((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim
  result = (sentences.filter (fun t => t.startsWith "I ")).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isBored_spec_satisfied (S : String) (h_precond : isBored_precond (S)) :
    isBored_postcond (S) (isBored (S) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
