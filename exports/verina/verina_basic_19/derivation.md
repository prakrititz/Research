# Derivation of verina_basic_19

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ a.size - 1 ∧ (ok = true ↔ ∀ k, k < i → a[k]! ≤ a[k + 1]!)`
  - guard: `i < a.size - 1`
  - variant: `a.size - 1 - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (a[i]! ≤ a[i + 1]!))`
