# Derivation of he_063_fibfib

kind: **loop**

- **loop** over state (i : Nat, a : Nat, b : Nat, c : Nat), start (0, 0, 0, 1)
  - invariant: `i ≤ n ∧ a = fibfibSpec i ∧ b = fibfibSpec (i + 1) ∧ c = fibfibSpec (i + 2)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `a`
  - helper lemma `fibfib_step`: `∀ (i : Nat), fibfibSpec (i + 3) = fibfibSpec (i + 2) + fibfibSpec (i + 1) + fibfibSpec i`
  - helper lemma `fibfib_base`: `fibfibSpec 0 = 0 ∧ fibfibSpec 1 = 0 ∧ fibfibSpec 2 = 1`
  - **term**: `(i + 1, b, c, a + b + c)`
