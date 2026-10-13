# Derivation of he_088_sort_array

kind: **restate**

- **cases** on `array ≠ [] ∧ (array.head! + array.getLast!) % 2 = 0`
  - helper lemma `sortNat_ok`: `∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!`
  - helper lemma `sortNatDesc_ok`: `∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≥ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≥ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (L.mergeSort (fun a b => decide (a ≥ b)))[i + 1]!`
  - _then_:
    - **term**: `array.mergeSort (fun a b => decide (a ≥ b))`
  - _else_:
    - **term**: `array.mergeSort (fun a b => decide (a ≤ b))`
