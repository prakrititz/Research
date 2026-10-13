# Derivation of verina_basic_17

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ s.length ∧ acc = (List.range i).map (fun j => (if isUpperCase s.toList[j]! then shift32 s.toList[j]! else s.toList[j]!))`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [(if isUpperCase s.toList[i]! then shift32 s.toList[i]! else s.toList[i]!)])`
