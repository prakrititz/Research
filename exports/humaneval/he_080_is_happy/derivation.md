# Derivation of he_080_is_happy

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ s.length - 2 ∧ (ok = true ↔ ∀ k, k < i → s.toList[k]! ≠ s.toList[k + 1]! ∧ s.toList[k]! ≠ s.toList[k + 2]! ∧ s.toList[k + 1]! ≠ s.toList[k + 2]!)`
  - guard: `i < s.length - 2`
  - variant: `s.length - 2 - i`
  - result: `decide (s.length ≥ 3) && ok`
  - **term**: `(i + 1, ok && decide (s.toList[i]! ≠ s.toList[i + 1]! ∧ s.toList[i]! ≠ s.toList[i + 2]! ∧ s.toList[i + 1]! ≠ s.toList[i + 2]!))`
