# Derivation of he_060_sum_to_n

kind: **loop**

- **loop** over state (i : Nat, s : Nat), start (0, 0)
  - invariant: `s * 2 = i * (i + 1) ∧ i ≤ n`
  - guard: `i < n`
  - variant: `n - i`
  - result: `s`
  - **term**: `(i + 1, s + (i + 1))`
