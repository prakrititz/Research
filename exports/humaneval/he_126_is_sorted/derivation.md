# Derivation of he_126_is_sorted

kind: **loop**

- **bind** `a : Bool` with property `a = true ↔ ∀ i, i < lst.length - 1 → lst[i]! ≤ lst[i + 1]!`
  - _value_:
    - **loop** over state (i : Nat, ok : Bool), start (0, true)
      - invariant: `i ≤ lst.length - 1 ∧ (ok = true ↔ ∀ k, k < i → lst[k]! ≤ lst[k + 1]!)`
      - guard: `i < lst.length - 1`
      - variant: `lst.length - 1 - i`
      - result: `ok`
      - **term**: `(i + 1, ok && decide (lst[i]! ≤ lst[i + 1]!))`
  - _continuation_:
    - **bind** `b : Bool` with property `b = true ↔ ∀ x ∈ lst, lst.count x ≤ 2`
      - _value_:
        - **loop** over state (i : Nat, ok : Bool), start (0, true)
          - invariant: `i ≤ lst.length ∧ (ok = true ↔ ∀ k, k < i → lst.count lst[k]! ≤ 2)`
          - guard: `i < lst.length`
          - variant: `lst.length - i`
          - result: `ok`
          - **term**: `(i + 1, ok && decide (lst.count lst[i]! ≤ 2))`
      - _continuation_:
        - **term**: `a && b`
