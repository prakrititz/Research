# Derivation of he_055_fib

kind: **loop**

- **loop** over state (i : Nat, a : Nat, b : Nat), start (0, 0, 1)
  - invariant: `i ≤ n ∧ a = fibSpec i ∧ b = fibSpec (i + 1)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `a`
  - **term**: `(i + 1, b, a + b)`
