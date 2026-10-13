# Derivation of he_105_by_length

kind: **restate**

- **bind** `ds : List Int` with property `ds = arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)`
  - _value_:
    - **term**: `arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)`
  - _continuation_:
    - **term**: `(ds.mergeSort (fun a b => a ≥ b)).map numName`
