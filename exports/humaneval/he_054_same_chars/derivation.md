# Derivation of he_054_same_chars

kind: **loop**

- **bind** `a : Bool` with property `a = true ↔ ∀ c ∈ s0.toList, c ∈ s1.toList`
  - _value_:
    - **loop** over state (i : Nat, ok : Bool), start (0, true)
      - invariant: `i ≤ s0.length ∧ (ok = true ↔ ∀ k, k < i → s0.toList[k]! ∈ s1.toList)`
      - guard: `i < s0.length`
      - variant: `s0.length - i`
      - result: `ok`
      - **term**: `(i + 1, ok && decide (s0.toList[i]! ∈ s1.toList))`
  - _continuation_:
    - **bind** `b : Bool` with property `b = true ↔ ∀ c ∈ s1.toList, c ∈ s0.toList`
      - _value_:
        - **loop** over state (i : Nat, ok : Bool), start (0, true)
          - invariant: `i ≤ s1.length ∧ (ok = true ↔ ∀ k, k < i → s1.toList[k]! ∈ s0.toList)`
          - guard: `i < s1.length`
          - variant: `s1.length - i`
          - result: `ok`
          - **term**: `(i + 1, ok && decide (s1.toList[i]! ∈ s0.toList))`
      - _continuation_:
        - **term**: `a && b`
