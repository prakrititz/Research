# Derivation of he_077_iscube

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ a.natAbs + 2 ∧ (f = true ↔ ∃ k, k < i ∧ k ^ 3 = a.natAbs)`
  - guard: `i < a.natAbs + 2`
  - variant: `a.natAbs + 2 - i`
  - result: `f`
  - **term**: `(i + 1, f || decide (i ^ 3 = a.natAbs))`
