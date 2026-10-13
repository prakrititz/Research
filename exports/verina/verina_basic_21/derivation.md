# Derivation of verina_basic_21

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ main.length + 1 ∧ (f = true ↔ ∃ k, k < i ∧ k + sub.length ≤ main.length ∧ sub = (main.drop k).take sub.length)`
  - guard: `i < main.length + 1`
  - variant: `main.length + 1 - i`
  - result: `f`
  - **term**: `(i + 1, f || decide (i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length))`
