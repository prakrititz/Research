# Derivation of he_014_all_prefixes

kind: **loop**

- **loop** over state (i : Nat, acc : List String), start (0, [])
  - invariant: `i ≤ string.length ∧ acc.length = i ∧ ∀ k, k < i → acc[k]! = String.mk (string.toList.take (k + 1))`
  - guard: `i < string.length`
  - variant: `string.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [String.mk (string.toList.take (i + 1))])`
