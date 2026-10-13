# Derivation of verina_basic_82

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ a.size - 1 ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = a[jj + 1]!`
  - guard: `i < a.size - 1`
  - variant: `a.size - 1 - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push a[i + 1]!)`
