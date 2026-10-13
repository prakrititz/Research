# Derivation of verina_basic_36

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ s.length ∧ acc = (List.range i).map (fun j => (if isSpaceCommaDot s.toList[j]! then ':' else s.toList[j]!))`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [(if isSpaceCommaDot s.toList[i]! then ':' else s.toList[i]!)])`
