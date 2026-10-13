# Derivation of he_072_will_it_fly

kind: **loop**

- **bind** `pal : Bool` with property `pal = true ↔ ∀ i, i < q.length → q[i]! = q[q.length - 1 - i]!`
  - _value_:
    - **loop** over state (i : Nat, ok : Bool), start (0, true)
      - invariant: `i ≤ q.length ∧ (ok = true ↔ ∀ k, k < i → q[k]! = q[q.length - 1 - k]!)`
      - guard: `i < q.length`
      - variant: `q.length - i`
      - result: `ok`
      - **term**: `(i + 1, ok && decide (q[i]! = q[q.length - 1 - i]!))`
  - _continuation_:
    - **term**: `pal && decide (q.sum ≤ w)`
