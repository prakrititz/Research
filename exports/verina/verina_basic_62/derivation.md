# Derivation of verina_basic_62

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ a.size ∧ ∀ i, i < n → a[i]! ≠ key`
  - guard: `n < a.size ∧ a[n]! ≠ key`
  - variant: `a.size - n`
  - result: `if n < a.size then (n : Int) else -1`
  - **term**: `n + 1`
