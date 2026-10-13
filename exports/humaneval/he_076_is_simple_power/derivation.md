# Derivation of he_076_is_simple_power

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ x.natAbs + 3 ∧ (f = true ↔ ∃ k, k < i ∧ 1 ≤ k ∧ n ^ k = x)`
  - guard: `i < x.natAbs + 3`
  - variant: `x.natAbs + 3 - i`
  - result: `decide (x = 1) || f`
  - **term**: `(i + 1, f || decide (1 ≤ i ∧ n ^ i = x))`
