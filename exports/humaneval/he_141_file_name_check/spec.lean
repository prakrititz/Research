import Mathlib

@[reducible, simp]
def fileNameCheck_precond (file_name : String) : Prop :=
  True

@[reducible, simp]
def fileNameCheck_postcond (file_name : String) (result: String) (h_precond : fileNameCheck_precond (file_name)) :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧
    ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧
      (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)))
