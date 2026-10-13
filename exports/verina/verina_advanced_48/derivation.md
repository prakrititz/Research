# Derivation of verina_advanced_48

kind: **restate**

- **term**: `list.mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `sorted_perm`: `∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort (fun a b => decide (a ≤ b))) ∧ List.isPerm l (l.mergeSort (fun a b => decide (a ≤ b))) = true`
