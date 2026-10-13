# Derivation of classic_sort_list

kind: **restate**

- **term**: `l.mergeSort (fun a b => a ≤ b)`
  - helper lemma `sort_ok`: `∀ (l : List Int), (∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ (l.mergeSort (fun a b => decide (a ≤ b))).isPerm l = true`
