# Derivation of verina_basic_22

kind: **restate**

- **term**: `(((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort (fun x y => decide (x ≤ y))).toArray)`
  - helper lemma `inArray_iff`: `∀ (a : Array Int) (x : Int), inArray a x = true ↔ x ∈ a.toList`
  - helper lemma `diss22`: `∀ (a b : Array Int) (h : dissimilarElements_precond a b), dissimilarElements_postcond a b (((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort (fun x y => decide (x ≤ y))).toArray) h`
