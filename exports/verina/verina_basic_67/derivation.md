# Derivation of verina_basic_67

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ x.length ∧ (ok = true ↔ ∀ k, k < i → x[k]! = x[x.length - k - 1]!)`
  - guard: `i < x.length`
  - variant: `x.length - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (x[i]! = x[x.length - i - 1]!))`
