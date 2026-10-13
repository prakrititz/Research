# Derivation of verina_basic_85

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ a.size ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = a[a.size - 1 - jj]!`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (a[a.size - 1 - i]!))`
