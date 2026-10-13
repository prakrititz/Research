# Derivation of he_093_encode

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ message.length ∧ acc = (List.range i).map (fun k => encChar message.toList[k]!)`
  - guard: `i < message.length`
  - variant: `message.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [encChar message.toList[i]!])`
