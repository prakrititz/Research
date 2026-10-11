-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def splitWhite (txt : String) : List String :=
  ((txt.map (fun c => if c == '\n' || c == '\r' || c == '\t' then ' ' else c)).splitOn " ").filter (fun w => w != "")
-- !benchmark @end precond_aux

@[reducible, simp]
def splitWords_precond (txt : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def splitWords (txt : String) (h_precond : splitWords_precond (txt)) : List String ⊕ Nat :=
  -- !benchmark @start code
  let hasWhite := txt.toList.any (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')
  if hasWhite then Sum.inl (splitWhite txt)
  else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",")
  else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 == 1)).length)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def splitWords_postcond (txt : String) (result: List String ⊕ Nat) (h_precond : splitWords_precond (txt)) :=
  -- !benchmark @start postcond
  let hasWhite := txt.toList.any (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')
  result = (if hasWhite then Sum.inl (splitWhite txt)
    else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",")
    else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 = 1)).length))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem splitWords_spec_satisfied (txt : String) (h_precond : splitWords_precond (txt)) :
    splitWords_postcond (txt) (splitWords (txt) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
