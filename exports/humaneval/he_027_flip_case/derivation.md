# Derivation of he_027_flip_case

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ string.length ∧ acc = (List.range i).map (fun k => flipChar string.toList[k]!)`
  - guard: `i < string.length`
  - variant: `string.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [flipChar string.toList[i]!])`
