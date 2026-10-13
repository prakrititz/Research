# Derivation of verina_basic_88

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ xs.length ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = xs[jj]!`
  - guard: `i < xs.length`
  - variant: `xs.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (xs[i]!))`
