# Derivation of verina_basic_10

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ a.size ∧ (ok = true ↔ ∀ k, k < i → n > a[k]!)`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (n > a[i]!))`
