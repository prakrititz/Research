# Derivation of verina_basic_13

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ a.size ∧ acc.size = i ∧ ∀ k, k < i → acc[k]! = a[k]! * a[k]! * a[k]!`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (a[i]! * a[i]! * a[i]!))`
