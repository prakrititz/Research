# Derivation of verina_basic_68

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ a.size ∧ ∀ i, i < n → a[i]! ≠ e`
  - guard: `n < a.size ∧ a[n]! ≠ e`
  - variant: `a.size - n`
  - result: `n`
  - **term**: `n + 1`
