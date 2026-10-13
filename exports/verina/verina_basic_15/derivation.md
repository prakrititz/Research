# Derivation of verina_basic_15

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ a.size - 1 ∧ (f = true ↔ ∃ k, k < i ∧ a[k]! + 1 = a[k + 1]!)`
  - guard: `i < a.size - 1`
  - variant: `a.size - 1 - i`
  - result: `f`
  - **term**: `(i + 1, f || decide (a[i]! + 1 = a[i + 1]!))`
