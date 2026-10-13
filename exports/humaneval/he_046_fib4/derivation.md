# Derivation of he_046_fib4

kind: **loop**

- **loop** over state (i : Nat, a : Nat, b : Nat, c : Nat, d : Nat), start (0, 0, 0, 2, 0)
  - invariant: `i ≤ n ∧ a = fib4Spec i ∧ b = fib4Spec (i + 1) ∧ c = fib4Spec (i + 2) ∧ d = fib4Spec (i + 3)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `a`
  - helper lemma `fib4_step`: `∀ (i : Nat), fib4Spec (i + 4) = fib4Spec (i + 3) + fib4Spec (i + 2) + fib4Spec (i + 1) + fib4Spec i`
  - helper lemma `fib4_base`: `fib4Spec 0 = 0 ∧ fib4Spec 1 = 0 ∧ fib4Spec 2 = 2 ∧ fib4Spec 3 = 0`
  - **term**: `(i + 1, b, c, d, a + b + c + d)`
