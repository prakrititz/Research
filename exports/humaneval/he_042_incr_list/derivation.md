# Derivation of he_042_incr_list

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `acc.length = i ∧ i ≤ l.length ∧ ∀ k, k < i → acc[k]! = l[k]! + 1`
  - guard: `i < l.length`
  - variant: `l.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [l[i]! + 1])`
