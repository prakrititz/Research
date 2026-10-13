# Derivation of verina_basic_58

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ s.size ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = 2 * s[jj]!`
  - guard: `i < s.size`
  - variant: `s.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (2 * s[i]!))`
