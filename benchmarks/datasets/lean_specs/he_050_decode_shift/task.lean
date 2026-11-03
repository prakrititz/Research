-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def shiftChar (c : Char) : Char := Char.ofNat ((c.toNat - 97 + 5) % 26 + 97)
-- !benchmark @end precond_aux

@[reducible, simp]
def decodeShift_precond (s : String) : Prop :=
  -- !benchmark @start precond
  s.toList.all (fun c => c.isLower) = true
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def decodeShift (s : String) (h_precond : decodeShift_precond (s)) : String :=
  -- !benchmark @start code
  String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def decodeShift_postcond (s : String) (result: String) (h_precond : decodeShift_precond (s)) :=
  -- !benchmark @start postcond
  result.toList.all (fun c => c.isLower) = true ∧ result.toList.map shiftChar = s.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem decodeShift_spec_satisfied (s : String) (h_precond : decodeShift_precond (s)) :
    decodeShift_postcond (s) (decodeShift (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
