# Derivation of verina_basic_84

kind: **loop**

- **loop** over state (i : Nat, acc : Array Int), start (0, #[])
  - invariant: `i ≤ arr.size ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = (if arr[jj]! > k then -1 else arr[jj]!)`
  - guard: `i < arr.size`
  - variant: `arr.size - i`
  - result: `acc`
  - **term**: `(i + 1, acc.push ((if arr[i]! > k then -1 else arr[i]!)))`
