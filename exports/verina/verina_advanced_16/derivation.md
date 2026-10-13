# Derivation of verina_advanced_16

kind: **restate**

- **term**: `xs.mergeSort (fun a b => a ≤ b)`
  - helper lemma `sorted_perm`: `∀ (xs : List Int), List.Pairwise (· ≤ ·) (xs.mergeSort (fun a b => decide (a ≤ b))) ∧ List.isPerm xs (xs.mergeSort (fun a b => decide (a ≤ b))) = true`
