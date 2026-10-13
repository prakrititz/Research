# Derivation of he_052_below_threshold

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ l.length ∧ (ok = true ↔ ∀ k, k < i → l[k]! < t)`
  - guard: `i < l.length`
  - variant: `l.length - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (l[i]! < t))`
