# Derivation of he_062_derivative

kind: **loop**

- **loop** over state (k : Nat, acc : List Int), start (0, [])
  - invariant: `k ≤ xs.length - 1 ∧ acc.length = k ∧ ∀ m, m < k → acc[m]! = xs[m + 1]! * ((m : Int) + 1)`
  - guard: `k < xs.length - 1`
  - variant: `xs.length - 1 - k`
  - result: `acc`
  - **term**: `(k + 1, acc ++ [xs[k + 1]! * ((k : Int) + 1)])`
