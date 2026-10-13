# Derivation of verina_basic_18

kind: **restate**

- **term**: `List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n)))`
