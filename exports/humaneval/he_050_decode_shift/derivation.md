# Derivation of he_050_decode_shift

kind: **restate**

- **term**: `String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))`
  - helper lemma `decode_shift_string`: `∀ (s : String), s.toList.all (fun c => c.isLower) = true → ((String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))).toList.all (fun c => c.isLower) = true ∧ (String.mk (s.toList.map (fun c => Char.ofNat ((c.toNat - 97 + 21) % 26 + 97)))).toList.map shiftChar = s.toList)`
