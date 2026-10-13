# Derivation of verina_basic_87

kind: **restate**

- **term**: `(a.toList.mergeSort (fun x y => decide (x ≤ y))).toArray`
  - helper lemma `sort_array_ok`: `∀ (l : List Int), List.Pairwise (· ≤ ·) ((l.mergeSort (fun x y => decide (x ≤ y))).toArray.toList) ∧ List.isPerm l ((l.mergeSort (fun x y => decide (x ≤ y))).toArray.toList) = true`
