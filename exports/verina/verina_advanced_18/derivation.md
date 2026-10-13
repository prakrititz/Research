# Derivation of verina_advanced_18

kind: **restate**

- **term**: `decide (n = List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList))`
