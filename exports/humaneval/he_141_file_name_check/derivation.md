# Derivation of he_141_file_name_check

kind: **restate**

- **cases** on `(file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧ ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧ (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)`
  - _then_:
    - **term**: `"Yes"`
  - _else_:
    - **term**: `"No"`
