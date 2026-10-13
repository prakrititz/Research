# Derivation of verina_basic_70

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ a.size ∧ ∀ k, k < n → ¬ P a[k]!`
  - guard: `n < a.size ∧ ¬ P a[n]!`
  - variant: `a.size - n`
  - result: `n`
  - **term**: `n + 1`
