# Derivation of he_100_make_a_pile

kind: **loop**

- **loop** over state (i : Nat, acc : List Nat), start (0, [])
  - invariant: `acc.length = i ∧ i ≤ n ∧ ∀ k, k < i → acc[k]! = n + 2 * k`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [n + 2 * i])`
