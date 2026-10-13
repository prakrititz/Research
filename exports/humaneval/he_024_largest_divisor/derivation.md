# Derivation of he_024_largest_divisor

kind: **loop**

- **loop** over state (d : Nat), start (n - 1)
  - invariant: `1 ≤ d ∧ d < n ∧ ∀ k, k < n → d < k → n % k ≠ 0`
  - guard: `n % d ≠ 0`
  - variant: `d`
  - result: `d`
  - **term**: `d - 1`
