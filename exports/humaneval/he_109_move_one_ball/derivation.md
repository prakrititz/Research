# Derivation of he_109_move_one_ball

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ arr.length + 1 ∧ (f = true ↔ ∃ k, k < i ∧ arr.drop k ++ arr.take k = arr.mergeSort (fun a b => a ≤ b))`
  - guard: `i < arr.length + 1`
  - variant: `arr.length + 1 - i`
  - result: `f`
  - **term**: `(i + 1, f || decide (arr.drop i ++ arr.take i = arr.mergeSort (fun a b => a ≤ b)))`
