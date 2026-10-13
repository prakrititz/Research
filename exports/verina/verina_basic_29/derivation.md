# Derivation of verina_basic_29

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ s.size - 1 ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = (if jj < k then s[jj]! else s[jj + 1]!)`
  - guard: `i < s.size - 1`
  - variant: `s.size - 1 - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push ((if i < k then s[i]! else s[i + 1]!)))`
