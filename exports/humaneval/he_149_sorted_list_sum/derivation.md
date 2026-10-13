# Derivation of he_149_sorted_list_sum

kind: **restate**

- **term**: `(lst.filter (fun s => decide (s.length % 2 = 0))).mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))`
  - helper lemma `sorted_ok`: `∀ (L : List String), (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).Perm L ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a)))).length - 1 → ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!.length < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]!.length ∨ ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!.length = (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]!.length ∧ ¬ ((L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i + 1]! < (L.mergeSort (fun a b => decide (a.length < b.length) || (a.length == b.length && !decide (b < a))))[i]!)))`
