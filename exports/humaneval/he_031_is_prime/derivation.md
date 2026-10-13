# Derivation of he_031_is_prime

kind: **loop**

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
