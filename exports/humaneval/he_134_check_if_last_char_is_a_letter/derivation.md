# Derivation of he_134_check_if_last_char_is_a_letter

kind: **restate**

- **term**: `decide (txt.length ≥ 1 ∧ txt.toList[txt.length - 1]!.isAlpha = true ∧ (txt.length = 1 ∨ txt.toList[txt.length - 2]! = ' '))`
