# Derivation of verina_advanced_51

kind: **restate**

- **term**: `(a ++ b).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `sorted_perm_rev`: `∀ (l : List Int), List.Pairwise (· ≤ ·) (l.mergeSort (fun a b => decide (a ≤ b))) ∧ List.isPerm (l.mergeSort (fun a b => decide (a ≤ b))) l = true`
