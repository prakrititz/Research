# Derivation of classic_isqrt

kind: **loop**

- **loop** over state (r : Nat), start (0)
  - invariant: `r * r ≤ n`
  - guard: `(r + 1) * (r + 1) ≤ n`
  - variant: `n - r`
  - result: `r`
  - **term**: `r + 1`
