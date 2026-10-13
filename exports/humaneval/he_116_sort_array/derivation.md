# Derivation of he_116_sort_array

kind: **restate**

- **term**: `arr.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))`
  - helper lemma `sort116_ok`: `∀ (L : List Int), (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b)))).length - 1 → (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! < ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∨ (ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! = ones (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]! ∧ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i]! ≤ (L.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && decide (a ≤ b))))[i + 1]!))`
