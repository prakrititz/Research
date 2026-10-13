# Derivation of verina_basic_53

kind: **loop**

- **loop** over state (i : Nat, s : Nat), start (0, 0)
  - invariant: `s * 2 = i * (i + 1) ∧ i ≤ N`
  - guard: `i < N`
  - variant: `N - i`
  - result: `s`
  - **term**: `(i + 1, s + (i + 1))`
