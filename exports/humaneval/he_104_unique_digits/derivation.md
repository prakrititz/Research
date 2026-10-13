# Derivation of he_104_unique_digits

kind: **restate**

- **term**: `(x.filter noEvenDigit).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `sortNat_ok`: `∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!`
