# Derivation of verina_advanced_69

kind: **loop**

- **loop** over state (n : Nat), start (0)
  - invariant: `n ≤ xs.length ∧ ∀ i, i < n → xs[i]! < target`
  - guard: `n < xs.length ∧ xs[n]! < target`
  - variant: `xs.length - n`
  - result: `n`
  - **term**: `n + 1`
