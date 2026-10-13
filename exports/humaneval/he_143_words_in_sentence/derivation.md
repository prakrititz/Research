# Derivation of he_143_words_in_sentence

kind: **restate**

- **term**: `" ".intercalate ((sentence.splitOn " ").filter (fun w => decide (Nat.Prime w.length)))`
