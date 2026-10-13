# Derivation of he_070_strange_sort_list

kind: **restate**

- **bind** `s : List Int` with property `s = lst.mergeSort (fun a b => a ≤ b)`
  - _value_:
    - **term**: `lst.mergeSort (fun a b => a ≤ b)`
  - _continuation_:
    - **term**: `(List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)`
