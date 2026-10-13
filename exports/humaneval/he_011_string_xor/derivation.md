# Derivation of he_011_string_xor

kind: **loop**

- **loop** over state (i : Nat, acc : List Char), start (0, [])
  - invariant: `i ≤ a.length ∧ acc = (List.range i).map (fun k => if a.toList[k]! = b.toList[k]! then '0' else '1')`
  - guard: `i < a.length`
  - variant: `a.length - i`
  - result: `String.mk acc`
  - **term**: `(i + 1, acc ++ [if a.toList[i]! = b.toList[i]! then '0' else '1'])`
