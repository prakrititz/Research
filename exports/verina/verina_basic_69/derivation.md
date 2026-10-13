# Derivation of verina_basic_69

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ a.size ∧ ∀ k, k < n → a[k]! ≠ e`
  - guard: `n < a.size ∧ a[n]! ≠ e`
  - variant: `a.size - n`
  - result: `n`
  - **term**: `n + 1`
