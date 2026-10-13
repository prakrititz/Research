# Derivation of he_084_solve

kind: **restate**

- **term**: `String.mk (Nat.toDigits 2 (((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum))`
  - helper lemma `toDigits2_binary`: `∀ (v : Nat), isBinary (Nat.toDigits 2 v) v`
  - helper lemma `binary_string_ok`: `∀ (s : Nat), isBinary (String.mk (Nat.toDigits 2 s)).toList s`
