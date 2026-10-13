# Derivation of he_091_is_bored

kind: **restate**

- **term**: `((((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim).filter (fun t => t.startsWith "I ") |>.length`
