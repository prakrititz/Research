# Derivation of he_120_maximum

kind: **restate**

- **term**: `((arr.mergeSort (fun a b => a ≥ b)).take k).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `sortInt_ok`: `∀ (L : List Int), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!`
