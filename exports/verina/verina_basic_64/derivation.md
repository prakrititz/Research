# Derivation of verina_basic_64

kind: **loop**

- **loop** over state (i : Nat, acc : Array Char), start (0, #[])
  - invariant: `i ≤ l + p ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = (if jj < atPos then oline[jj]! else if jj < atPos + p then nl[jj - atPos]! else oline[jj - p]!)`
  - guard: `i < l + p`
  - variant: `l + p - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push (if i < atPos then oline[i]! else if i < atPos + p then nl[i - atPos]! else oline[i - p]!))`
