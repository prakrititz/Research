# Derivation of verina_advanced_17

kind: **restate**

- **term**: `l.mergeSort (fun a b => a ≤ b)`
  - helper lemma `sorted_perm`: `∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort (fun a b => decide (a ≤ b))) ∧ List.isPerm l (l.mergeSort (fun a b => decide (a ≤ b))) = true`
