# Derivation of verina_basic_49

kind: **loop**

- **bind** `p : Nat` with property `p ≤ a.size ∧ (∀ j, j < p → ¬ isOdd a[j]! = true) ∧ (p < a.size → isOdd a[p]! = true)`
  - _value_:
    - **loop** over state (n : Nat), start (0)
      - invariant: `n ≤ a.size ∧ ∀ j, j < n → ¬ isOdd a[j]! = true`
      - guard: `n < a.size ∧ ¬ isOdd a[n]! = true`
      - variant: `a.size - n`
      - result: `n`
      - **term**: `n + 1`
  - _continuation_:
    - **cases** on `p < a.size`
      - _then_:
        - **term**: `some p`
      - _else_:
        - **term**: `none`
