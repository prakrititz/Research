# Derivation of verina_basic_37

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ arr.size ∧ ∀ i, i < n → arr[i]! ≠ target`
  - guard: `n < arr.size ∧ arr[n]! ≠ target`
  - variant: `arr.size - n`
  - result: `if n < arr.size then (n : Int) else -1`
  - **term**: `n + 1`
