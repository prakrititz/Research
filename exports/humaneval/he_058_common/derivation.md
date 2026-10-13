# Derivation of he_058_common

kind: **restate**

- **term**: `((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))`
  - helper lemma `common_sorted_ok`: `∀ (l1 l2 : List Int), (∀ i, i < (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))).length - 1 → (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)))[i]! < (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ (∀ x ∈ ((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)), x ∈ l1 ∧ x ∈ l2) ∧ ∀ x ∈ l1, x ∈ l2 → x ∈ ((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))`
