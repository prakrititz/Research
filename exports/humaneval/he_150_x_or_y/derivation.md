# Derivation of he_150_x_or_y

kind: **loop**

- **bind** `p : Bool` with property `p = true ↔ primeSpec n`
  - _value_:
    - **cases** on `n < 2`
      - _then_:
        - **term**: `false`
      - _else_:
        - **loop** over state (d : Nat, ok : Bool), start (2, true)
          - invariant: `2 ≤ d ∧ d ≤ n ∧ (ok = true ↔ ∀ k, k < d → k ≥ 2 → n % k ≠ 0)`
          - guard: `d < n`
          - variant: `n - d`
          - result: `ok`
          - **term**: `(d + 1, ok && decide (n % d ≠ 0))`
  - _continuation_:
    - **cases** on `p = true`
      - _then_:
        - **term**: `x`
      - _else_:
        - **term**: `y`
