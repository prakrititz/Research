# Derivation of he_123_get_odd_collatz

kind: **restate**

- **term**: `((collatzSeq 5000 n).filter (fun x => x % 2 = 1)).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `sortNat_ok`: `∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!`
