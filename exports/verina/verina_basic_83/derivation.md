# Derivation of verina_basic_83

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ a.size + b.size ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = (if jj < a.size then a[jj]! else b[jj - a.size]!)`
  - guard: `i < a.size + b.size`
  - variant: `a.size + b.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push ((if i < a.size then a[i]! else b[i - a.size]!)))`
