# Derivation of verina_advanced_50

kind: **restate**

- **term**: `((a1.toList ++ a2.toList).mergeSort (fun x y => decide (x ≤ y))).toArray`
  - helper lemma `ms50`: `∀ (a1 a2 : Array Nat) (h : mergeSorted_precond a1 a2), mergeSorted_postcond a1 a2 (((a1.toList ++ a2.toList).mergeSort (fun x y => decide (x ≤ y))).toArray) h`
