# Derivation of he_079_decimal_to_binary

kind: **restate**

- **term**: `String.mk (['d', 'b'] ++ Nat.toDigits 2 decimal ++ ['d', 'b'])`
  - helper lemma `toDigits2_binary`: `∀ (v : Nat), isBinary (Nat.toDigits 2 v) v`
  - helper lemma `toDigits2_ne_nil`: `∀ (v : Nat), Nat.toDigits 2 v ≠ []`
  - helper lemma `db_ok`: `∀ (v : Nat), ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length ≥ 5 ∧ (String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.take 2 = ['d', 'b'] ∧ (String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.drop ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length - 2) = ['d', 'b'] ∧ isBinary (((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.drop 2).take ((String.mk (['d', 'b'] ++ Nat.toDigits 2 v ++ ['d', 'b'])).toList.length - 4)) v)`
