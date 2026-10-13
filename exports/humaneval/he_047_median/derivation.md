# Derivation of he_047_median

kind: **restate**

- **bind** `s : List ℚ` with property `s = l.mergeSort (fun a b => a ≤ b)`
  - _value_:
    - **term**: `l.mergeSort (fun a b => a ≤ b)`
  - _continuation_:
    - **term**: `if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2`
