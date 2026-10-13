# Derivation of he_131_digits

kind: **restate**

- **term**: `if ((toString n).toList.map (fun c => c.toNat - 48)).any (fun d => d % 2 = 1) then (((toString n).toList.map (fun c => c.toNat - 48)).filter (fun d => d % 2 = 1)).prod else 0`
