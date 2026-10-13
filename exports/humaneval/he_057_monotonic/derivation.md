# Derivation of he_057_monotonic

kind: **loop**

- **bind** `up : Bool` with property `up = true ↔ ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!`
  - _value_:
    - **loop** over state (i : Nat, ok : Bool), start (0, true)
      - invariant: `i ≤ l.length - 1 ∧ (ok = true ↔ ∀ k, k < i → l[k]! ≤ l[k + 1]!)`
      - guard: `i < l.length - 1`
      - variant: `l.length - 1 - i`
      - result: `ok`
      - **term**: `(i + 1, ok && decide (l[i]! ≤ l[i + 1]!))`
  - _continuation_:
    - **bind** `down : Bool` with property `down = true ↔ ∀ i, i < l.length - 1 → l[i]! ≥ l[i + 1]!`
      - _value_:
        - **loop** over state (i : Nat, ok : Bool), start (0, true)
          - invariant: `i ≤ l.length - 1 ∧ (ok = true ↔ ∀ k, k < i → l[k]! ≥ l[k + 1]!)`
          - guard: `i < l.length - 1`
          - variant: `l.length - 1 - i`
          - result: `ok`
          - **term**: `(i + 1, ok && decide (l[i]! ≥ l[i + 1]!))`
      - _continuation_:
        - **term**: `up || down`
