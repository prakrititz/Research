# Derivation of he_089_encrypt

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ s.length ∧ acc = (List.range i).map (fun k => rot4 s.toList[k]!)`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [rot4 s.toList[i]!])`
