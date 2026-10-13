# Derivation of verina_basic_31

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ s.length ∧ acc = (List.range i).map (fun j => (if isLowerCase s.toList[j]! then shiftMinus32 s.toList[j]! else s.toList[j]!))`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [(if isLowerCase s.toList[i]! then shiftMinus32 s.toList[i]! else s.toList[i]!)])`
