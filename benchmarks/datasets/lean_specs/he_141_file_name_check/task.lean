-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def fileNameCheck_precond (file_name : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fileNameCheck (file_name : String) (h_precond : fileNameCheck_precond (file_name)) : String :=
  -- !benchmark @start code
  let parts := file_name.splitOn "."
  if (file_name.toList.filter Char.isDigit).length > 3 then "No"
  else if parts.length != 2 then "No"
  else if parts[0]! = "" then "No"
  else if !(parts[0]!.toList[0]!).isAlpha then "No"
  else if parts[1]! = "txt" || parts[1]! = "exe" || parts[1]! = "dll" then "Yes" else "No"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fileNameCheck_postcond (file_name : String) (result: String) (h_precond : fileNameCheck_precond (file_name)) :=
  -- !benchmark @start postcond
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧
    ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧
      (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fileNameCheck_spec_satisfied (file_name : String) (h_precond : fileNameCheck_precond (file_name)) :
    fileNameCheck_postcond (file_name) (fileNameCheck (file_name) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
