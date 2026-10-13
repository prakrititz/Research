# Derivation of verina_basic_65

kind: **loop**

- **loop** over state (r : Nat), start (0)
  - invariant: `r * r ≤ N`
  - guard: `(r + 1) * (r + 1) ≤ N`
  - variant: `N - r`
  - result: `r`
  - **term**: `r + 1`
