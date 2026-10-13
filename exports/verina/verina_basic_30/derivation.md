# Derivation of verina_basic_30

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → acc[k]! = a[k]! % b[k]!`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (a[i]! % b[i]!))`
