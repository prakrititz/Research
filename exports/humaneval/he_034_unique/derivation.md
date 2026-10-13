# Derivation of he_034_unique

kind: **restate**

- **term**: `(l.dedup).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `unique_sorted_ok`: `∀ (l : List Int), (∀ i, i < ((l.dedup).mergeSort (fun a b => decide (a ≤ b))).length - 1 → ((l.dedup).mergeSort (fun a b => decide (a ≤ b)))[i]! < ((l.dedup).mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ (∀ x ∈ (l.dedup).mergeSort (fun a b => decide (a ≤ b)), x ∈ l) ∧ ∀ x ∈ l, x ∈ (l.dedup).mergeSort (fun a b => decide (a ≤ b))`
